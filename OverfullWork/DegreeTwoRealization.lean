module

public import OverfullWork.CapacityTwo
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section


/-! # Simple realizations of degrees zero, one and two

The two vertices of degree two and no other positive degrees are the
only balanced even sequence not realizable by a simple graph.
-/
namespace OverfullWork.DegreeTwoRealization
open SimpleGraph Finset
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge SimpleGraph.instDecidableMapAdj
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_edge_exact (u v w : V) (huv : u≠v) :
    (edge u v).degree w=if w=u ∨ w=v then 1 else 0 := by
  rw [←card_neighborFinset_eq_degree]
  by_cases hu : w=u
  · subst w
    have he : (edge u v).neighborFinset u={v} := by
      ext z
      simp only [mem_neighborFinset,edge_adj,mem_singleton]; constructor <;> aesop
    simp [he]
  · by_cases hv : w=v
    · subst w
      have he : (edge u v).neighborFinset v={u} := by
        ext z
        simp only [mem_neighborFinset,edge_adj,mem_singleton]; constructor <;> aesop
      simp [he]
    · have he : (edge u v).neighborFinset w=∅ := by
        ext z
        simp [mem_neighborFinset,edge_adj,hu,hv]
      simp [he,hu,hv]

/-- Subdivide an existing edge through an isolated vertex. -/
theorem exists_subdivision (J : SimpleGraph V) (w u v : V)
    (hw : J.degree w=0) (huv : J.Adj u v) :
    ∃ K : SimpleGraph V,∀ z,K.degree z=if z=w then 2 else J.degree z := by
  classical
  have huw : u≠w := by
    intro h
    subst u
    have hh:=huv.degree_pos_left
    omega
  have hvw : v≠w := by
    intro h
    subst v
    have hh:=huv.degree_pos_right
    omega
  have huvne : u≠v:=huv.ne
  let B:=J \ edge u v
  have hsub : edge u v≤J:=by
    intro a b h
    rcases ((edge_adj _ _ _ _).mp h).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact huv
    · exact huv.symm
  have hB (z : V) : B.degree z+(if z=u ∨ z=v then 1 else 0)=J.degree z := by
    have hh:=Plantholt.degree_sdiff_add J hsub z
    rwa [degree_edge_exact u v z huvne] at hh
  have hBw : B.degree w=0:=by have hh:=hB w;omega
  have hdis₁ : Disjoint B (edge u w) := by
    rw [SimpleGraph.disjoint_left]
    intro a b hB hE
    have hJ : J.Adj a b:=hB.1
    rcases ((edge_adj _ _ _ _).mp hE).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have hh:=hJ.degree_pos_right;omega
    · have hh:=hJ.degree_pos_left;omega
  have hdis₂ : Disjoint (B⊔edge u w) (edge v w) := by
    rw [SimpleGraph.disjoint_left]
    intro a b hB hE
    rcases hB with hB|hB
    · have hJ : J.Adj a b:=hB.1
      rcases ((edge_adj _ _ _ _).mp hE).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · have hh:=hJ.degree_pos_right;omega
      · have hh:=hJ.degree_pos_left;omega
    · have h₁:=((edge_adj _ _ _ _).mp hB).1
      have h₂:=((edge_adj _ _ _ _).mp hE).1
      rcases h₁ with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
        rcases h₂ with ⟨h₁,h₂⟩|⟨h₁,h₂⟩ <;> simp_all
  refine ⟨(B⊔edge u w)⊔edge v w,?_⟩
  intro z
  rw [CapacityTwo.degree_union _ _ hdis₂,CapacityTwo.degree_union _ _ hdis₁,
    degree_edge_exact u w z huw,degree_edge_exact v w z hvw]
  have hh:=hB z
  by_cases hz : z=w
  · subst z
    simp only [if_pos,or_true]
    omega
  · rw [if_neg hz]
    by_cases hzu : z=u
    · subst z
      simp [huvne,huw] at hh ⊢
      omega
    · by_cases hzv : z=v
      · subst z
        simp [huvne.symm,hvw] at hh ⊢
        omega
      · simp [hzu,hzv,hz] at hh ⊢
        omega

/-- Degree-one endpoints supply a nonempty matching, and every requested
degree-two vertex is inserted by edge subdivision. -/
theorem exists_with_endpoints (S T : Finset V) (hdis : Disjoint S T)
    (heven : Even T.card) (hne : T.Nonempty) :
    ∃ J : SimpleGraph V,∀ v,J.degree v=(if v∈S then 2 else 0)+(if v∈T then 1 else 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hdirac : ∀ v∈T,T.card≤2*(Plantholt.nbIn (⊤ : SimpleGraph V) T v).card := by
      intro v hv
      have hnb : Plantholt.nbIn (⊤ : SimpleGraph V) T v=T.erase v := by
        ext z
        simp [Plantholt.nbIn,mem_neighborFinset,ne_comm]
      rw [hnb,card_erase_of_mem hv]
      have ht:=hne.card_pos
      obtain ⟨k,hk⟩:=heven
      omega
    obtain ⟨J,_,hJ,hJzero⟩:=Plantholt.exists_matchingOn (⊤ : SimpleGraph V) heven hdirac
    refine ⟨J,?_⟩
    intro v
    by_cases hv : v∈T
    · simpa [hv] using hJ v hv
    · simpa [hv] using hJzero v hv
  | @insert w S hw ih =>
    have hdis' : Disjoint S T:=disjoint_of_subset_left (subset_insert _ _) hdis
    obtain ⟨J,hJ⟩:=ih hdis'
    have hwT : w∉T:=fun hh => (disjoint_left.mp hdis) (mem_insert_self _ _) hh
    have hJw : J.degree w=0:=by simp [hJ,hw,hwT]
    obtain ⟨u,hu⟩:=hne
    have hpos : 0<J.degree u:=by rw [hJ,if_pos hu];omega
    obtain ⟨v,huv⟩:=(J.degree_pos_iff_exists_adj u).mp hpos
    obtain ⟨K,hK⟩:=exists_subdivision J w u v hJw huv
    refine ⟨K,?_⟩
    intro z
    rw [hK]
    by_cases hz : z=w
    · subst z
      simp [hwT]
    · simp [hz,hJ]

omit [DecidableEq V] in
theorem degree_map_embedding {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (f : W ↪ V) (w : W) :
    (H.map f).degree (f w)=H.degree w := by
  classical
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  have he : (H.map f).neighborFinset (f w)=(H.neighborFinset w).map f := by
    ext v
    simp only [mem_neighborFinset,map_adj,mem_map]
    constructor
    · rintro ⟨a,b,hab,ha,rfl⟩
      have haw : a=w:=f.injective ha
      exact ⟨b,haw ▸ hab,rfl⟩
    · rintro ⟨b,hab,rfl⟩
      exact ⟨w,b,hab,rfl,rfl⟩
  rw [he,card_map]

/-- A cycle realizes any set of at least three degree-two vertices. -/
theorem exists_cycle_on (S : Finset V) (hS : 3≤S.card) :
    ∃ J : SimpleGraph V,∀ v,J.degree v=if v∈S then 2 else 0 := by
  classical
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp : Fintype.card S=S.card)).symm
  let f : Fin S.card ↪ V:=e.toEmbedding.trans (Function.Embedding.subtype _)
  let J:=(cycleGraph S.card).map f
  refine ⟨J,?_⟩
  intro v
  by_cases hv : v∈S
  · rw [if_pos hv]
    let w:=e.symm ⟨v,hv⟩
    have hfw : f w=v:=by simp [f,w]
    rw [←hfw]
    change ((cycleGraph S.card).map f).degree (f w)=2
    rw [degree_map_embedding]
    have hcycle (n : ℕ) (hn : 3≤n) (z : Fin n) : (cycleGraph n).degree z=2 := by
      match n with
      | 0 | 1 | 2 => omega
      | n+3 => exact cycleGraph_degree_three_le
    refine Eq.trans ?_ (hcycle S.card hS w)
    unfold SimpleGraph.degree
    congr 1
    ext z
    simp only [mem_neighborFinset]
  · rw [if_neg hv,←card_neighborFinset_eq_degree,card_eq_zero]
    ext z
    simp only [mem_neighborFinset,notMem_empty,iff_false]
    intro h
    obtain ⟨a,b,_,ha,_⟩:=(map_adj f (cycleGraph S.card) v z).mp h
    exact hv (ha ▸ (e a).2)

/-- A balanced even sequence bounded by two is simple, apart from the
explicit sequence consisting of two twos. No graph-density input is used. -/
theorem exists_simple_or_exception (a : V → ℕ) (ha : ∀ v,a v≤2)
    (heven : Even (∑ v,a v)) (hbalance : ∀ v,2*a v≤∑ w,a w) :
    (∃ J : SimpleGraph V,∀ v,J.degree v=a v) ∨
      ∃ u v : V,u≠v ∧ ∀ w,a w=if w=u ∨ w=v then 2 else 0 := by
  classical
  let S:=univ.filter (fun v => a v=2)
  let T:=univ.filter (fun v => a v=1)
  have hsplit (v : V) : a v=(if v∈S then 2 else 0)+(if v∈T then 1 else 0) := by
    have hh:=ha v
    simp only [S,T,mem_filter,mem_univ,true_and]
    split_ifs <;> omega
  have hsum : (∑ v,a v)=2*S.card+T.card := by
    have hs : (∑ v : V,if v∈S then 2 else 0)=2*S.card := by
      rw [←sum_filter]
      simp [Nat.mul_comm]
    have ht : (∑ v : V,if v∈T then 1 else 0)=T.card := by
      rw [←sum_filter]
      simp
    calc
      _ = ∑ v : V,((if v∈S then 2 else 0)+(if v∈T then 1 else 0)) :=
        sum_congr rfl (fun v _ => hsplit v)
      _ = _ := by rw [sum_add_distrib,hs,ht]
  have hTeven : Even T.card := by
    obtain ⟨k,hk⟩:=heven
    refine ⟨T.card/2,?_⟩
    omega
  have hdis : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    have hs:=(mem_filter.mp hvS).2
    have ht:=(mem_filter.mp hvT).2
    omega
  by_cases ht : T.Nonempty
  · obtain ⟨J,hJ⟩:=exists_with_endpoints S T hdis hTeven ht
    exact Or.inl ⟨J,fun v => (hJ v).trans (hsplit v).symm⟩
  · have hTempty : T=∅:=not_nonempty_iff_eq_empty.mp ht
    have hav (v : V) : a v=if v∈S then 2 else 0:=by simpa [hTempty] using hsplit v
    by_cases hzero : S.card=0
    · have hSempty : S=∅:=card_eq_zero.mp hzero
      exact Or.inl ⟨⊥,fun v => by simp [hav,hSempty]⟩
    · by_cases hone : S.card=1
      · obtain ⟨u,hu⟩:=card_pos.mp (by omega : 0<S.card)
        have hau : a u=2:=(mem_filter.mp hu).2
        have hh:=hbalance u
        simp only [hsum,hTempty,card_empty,hau,hone] at hh
        omega
      · by_cases htwo : S.card=2
        · obtain ⟨u,v,huv,hS⟩:=card_eq_two.mp htwo
          exact Or.inr ⟨u,v,huv,fun w => by simp [hav,hS]⟩
        · obtain ⟨J,hJ⟩:=exists_cycle_on S (by omega)
          exact Or.inl ⟨J,fun v => (hJ v).trans (hav v).symm⟩

end OverfullWork.DegreeTwoRealization
