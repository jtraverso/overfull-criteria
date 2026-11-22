module

public import OverfullWork.CriticalLowPartnerProjection
public import OverfullWork.LowSkeletonLayerGluing
public import OverfullWork.LowSkeletonAttachmentDegrees
public import OverfullWork.PathGraphRealization

@[expose] public section


/-! # Uniform actual core paths for the even low-vertex case

The proved critical deficit theorem chooses the scale before the graph.
An actual low-saturating matching and its actual projection are reserved
before constructing disjoint spanning core paths. The output walks use
only original edges outside both reserved matchings.
This covers the explicit case of an even low set of size at least two.
-/
namespace OverfullWork.CriticalCorePathPreparation
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open PaperLowSkeleton LowSkeletonPreparation LowSkeletonProjection
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

/-- All paths and representatives belong to one actual matching choice. -/
structure EvenPrepared (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) where
  M : SimpleGraph V
  skeleton : IsSkeleton G M (lowVertices G)
  matching : OneFactor.IsMatchingGraph M
  low_degree_one : ∀w∈lowVertices G,M.degree w=1
  low_subset : lowVertices G⊆U
  projection : Projection G (outerLeaves M (lowVertices G)) U (nonisolatedVertices M)
  h : ℕ
  positive : 1≤h
  count_le : h≤k
  e : (Fin h×Bool)≃ outerLeaves M (lowVertices G)
  paths : ∀i,G.Walk (projection.representative (e (i,false))).val
    (projection.representative (e (i,true))).val
  paths_simple : ∀i,(paths i).IsPath
  paths_disjoint : ∀i j,i≠j → ∀v,v∈(paths i).support → v∉(paths j).support
  paths_cover : ∀v,v∉U → ∃i,v∈(paths i).support
  paths_off : ∀i,∀v∈(paths i).support,v∉U
  paths_avoid : ∀i,∀a b,(PathGraphRealization.pathGraph (paths i)).Adj a b →
    ¬(M⊔projection.matching).Adj a b
  attachment_core_degree : ∀v,v∉U → (M⊔projection.matching).degree v=
    if ∃a : outerLeaves M (lowVertices G),(projection.representative a).val=v then 1 else 0

/-- G1, matching selection, projection and dense path extension are all
discharged here. The order threshold is chosen before the vertex type. -/
theorem above_half_even_core_path_preparation (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        Even (lowVertices G).card → 2≤(lowVertices G).card →
        let k:=Fintype.card V/(4096*q^2)
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        U.card≤k ∧ Nonempty (EvenPrepared G U k) := by
  obtain ⟨q,hq,N,htrim⟩:=
    CriticalDenseCoreTrimming.above_half_critical_sparse_trimming.{u} ε hε
  refine ⟨q,hq,max N (2*4096*q^2),?_⟩
  intro V _ _ G _ hn hc hdense heven htwo
  let n:=Fintype.card V
  let a:=n/(8*q)
  let k:=n/(4096*q^2)
  let W:=lowVertices G
  let U:=exceptions G G.maxDegree a
  obtain ⟨_,hUk,htr⟩:=htrim G ((le_max_left _ _).trans hn) hc hdense
  change U.card≤k at hUk
  change U.card≤k ∧ Nonempty (EvenPrepared G U k)
  refine ⟨hUk,?_⟩
  have hn2 : 2*(4096*q^2)≤n := by
    have hh:=(le_max_right N (2*4096*q^2)).trans hn
    simpa only [n,Nat.mul_assoc] using hh
  have hk : 2≤k := (Nat.le_div_iff_mul_le (by positivity)).mpr hn2
  have hnscale : 4096*q^2≤n := by omega
  obtain ⟨_,_,hscale,_,_⟩:=RobustExpansion.sparse_deficit_integer_scales n q hq hnscale
  change 2*k+1≤a at hscale
  have hnD : n≤2*G.maxDegree := by
    have he : 0≤ε*(n:ℝ) := by positivity
    exact_mod_cast (show (n:ℝ)≤2*(G.maxDegree:ℝ) by nlinarith only [hdense,he])
  have haf : 8*q*a≤n := Nat.mul_div_le n (8*q)
  have h16 : 16*a≤n := (Nat.mul_le_mul_right a (by omega : 16≤8*q)).trans haf
  have haD : 8*a≤G.maxDegree := by omega
  have hD : 0<G.maxDegree := by omega
  have hWU : W⊆U := CriticalLowPartnerProjection.lowVertices_subset_exceptions G a hD haD
  have hWk : W.card≤k := (card_le_card hWU).trans hUk
  obtain ⟨M,hs,hm⟩:=LowSkeletonLayerGluing.exists_even_matching_skeleton G hc htwo heven
  have hout : ∀v∉W,M.degree v≤1 := fun v _ => matching_degree_le_one M hm v
  have hone : ∀w∈W,M.degree w=1 := by
    intro w hw
    have hlow:=hs.low_positive w hw
    have hhigh:=matching_degree_le_one M hm w
    omega
  let A:=outerLeaves M W
  let Z:=nonisolatedVertices M
  have hA : A.card≤W.card+1 := hs.outer_card_le
  have hZ : Z.card≤2*(W.card+1) :=
    (nonisolatedVertices_card_le_twice_edges M).trans (Nat.mul_le_mul_left 2 hs.edge_bound)
  obtain ⟨P⟩:=CriticalLowPartnerProjection.exists_projection_avoiding_of_low_partners
    G hc a k hD haD hscale hUk A Z hA hZ (fun x hx => hs.outer_neighbour hx)
  let Q:=M⊔P.matching
  have hQG : Q≤G := LowSkeletonAttachmentDegrees.attachment_le hs.le_graph P
  have hQ : Q.maxDegree≤2 := Q.maxDegree_le_of_forall_degree_le 2
    (LowSkeletonAttachmentDegrees.degree_le_two hWU hs.crosses hs.degree_le_two hout P)
  have hApos : 0<A.card := by have hl : 2≤A.card:=hs.outer_two_le;omega
  obtain ⟨h,hh,hAh,⟨e⟩⟩:=PairedEndpointEnumeration.exists_pairing A hs.outer_even hApos
  have hhk : h≤k := by omega
  rcases h with _|t
  · omega
  let C : Set V:=(U : Set V)ᶜ
  let K:=(G\Q).induce C
  let ρ : A → C:=fun x => ⟨(P.representative x).val,mem_compl.mp (P.representative x).property⟩
  have hρ : Function.Injective ρ := by
    intro x y he
    apply P.injective
    exact Subtype.ext (congrArg (fun z:C => z.val) he)
  let left : Fin (t+1) → C:=fun i => ρ (e (i,false))
  let right : Fin (t+1) → C:=fun i => ρ (e (i,true))
  have hleft : Function.Injective left := by
    intro i j he
    exact congrArg Prod.fst (e.injective (hρ he))
  have hright : Function.Injective right := by
    intro i j he
    exact congrArg Prod.fst (e.injective (hρ he))
  have hcross : ∀i j,left i≠right j := by
    intro i j he
    have hb:=congrArg Prod.snd (e.injective (hρ he))
    exact Bool.false_ne_true hb
  obtain ⟨hdeg,hsize⟩:=htr Q hQG (hQ.trans (by omega : 2≤k))
  change Fintype.card C+6*k+2≤2*K.minDegree at hdeg
  change 3*k+5≤Fintype.card C at hsize
  obtain ⟨paths,hpaths,hdis,hcov⟩:=DenseHamilton.exists_paths t K left right hcross hleft hright
    (by omega) (by omega)
  let f : K →g G:={ toFun:=Subtype.val,map_rel':=fun h => h.1 }
  have hf : Function.Injective f := Subtype.val_injective
  let ambient:=fun i => (paths i).map f
  have has : ∀i,(ambient i).IsPath:=fun i => (hpaths i).map hf
  have hsupport : ∀i,∀v,v∈(ambient i).support ↔ ∃w∈(paths i).support,w.val=v := by
    intro i v
    rw [Walk.support_map,List.mem_map]
    rfl
  have had : ∀i j,i≠j → ∀v,v∈(ambient i).support → v∉(ambient j).support := by
    intro i j hij v hvi hvj
    obtain ⟨x,hx,rfl⟩:=(hsupport i v).mp hvi
    obtain ⟨y,hy,he⟩:=(hsupport j x.val).mp hvj
    have heq : y=x := Subtype.ext he
    subst y
    exact hdis i j hij x hx hy
  have hco : ∀v,v∉U → ∃i,v∈(ambient i).support := by
    intro v hv
    obtain ⟨i,hi⟩:=hcov ⟨v,hv⟩
    exact ⟨i,(hsupport i v).mpr ⟨⟨v,hv⟩,hi,rfl⟩⟩
  have hoff : ∀i,∀v∈(ambient i).support,v∉U := by
    intro i v hv
    obtain ⟨w,_,rfl⟩:=(hsupport i v).mp hv
    exact w.property
  have havoid : ∀i,∀z w,(PathGraphRealization.pathGraph (ambient i)).Adj z w → ¬Q.Adj z w := by
    intro i z w hzw
    have he : s(z,w)∈((paths i).map f).edges := Walk.adj_toSubgraph_iff_mem_edges.mp hzw
    rw [Walk.edges_map,List.mem_map] at he
    obtain ⟨edge,hedge,heq⟩:=he
    induction edge using Sym2.inductionOn with
    | hf x y =>
      have hxy:= (paths i).adj_of_mem_edges hedge
      have hh : ¬Q.Adj x.val y.val := hxy.2
      have heq' : s(x.val,y.val)=s(z,w) := heq
      rcases Sym2.eq_iff.mp heq' with ⟨hx,hy⟩|⟨hx,hy⟩
      · simpa only [hx,hy] using hh
      · simpa only [hx,hy,Q.adj_comm] using hh
  exact ⟨{
    M:=M,skeleton:=hs,matching:=hm,low_degree_one:=hone,low_subset:=hWU,
    projection:=P,h:=t+1,positive:=hh,count_le:=hhk,e:=e,paths:=ambient,
    paths_simple:=has,paths_disjoint:=had,paths_cover:=hco,paths_off:=hoff,paths_avoid:=havoid,
    attachment_core_degree:=fun v hv =>
      LowSkeletonAttachmentDegrees.degree_on_core hWU hs.crosses hout P hv }⟩

end OverfullWork.CriticalCorePathPreparation
