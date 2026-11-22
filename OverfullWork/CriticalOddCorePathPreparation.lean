module

public import OverfullWork.CriticalCorePathPreparation
public import OverfullWork.OddLowSkeletonWitness

@[expose] public section


/-! # Uniform actual core paths for the odd low-vertex case

The actual matching, its fresh extra edge and their two distinguished
outside arms are retained. Pairing those arms in different pairs prevents
the prescribed core paths from joining them to each other.
All matching, projection and path choices are constructed from G1 and
criticality, with the scale fixed before the graph.
-/
namespace OverfullWork.CriticalOddCorePathPreparation
open SimpleGraph Finset SparseDeficitCore LowVertexMatchingAbsorption
open PaperLowSkeleton LowSkeletonPreparation LowSkeletonProjection
open scoped Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

structure OddPrepared (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) where
  M : SimpleGraph V
  w : V
  a : V
  b : V
  base_le : M≤G
  base_matching : OneFactor.IsMatchingGraph M
  base_cover : ∀v∈lowVertices G,∃!z,M.Adj v z
  base_cross : ∀u v,M.Adj u v → (u∈lowVertices G ∧ v∉lowVertices G) ∨ (v∈lowVertices G ∧ u∉lowVertices G)
  w_low : w∈lowVertices G
  matched_arm : M.Adj w a
  fresh_outside : b∉lowVertices G
  fresh_degree_zero : M.degree b=0
  extra_arm : G.Adj w b
  skeleton : IsSkeleton G (M⊔edge w b) (lowVertices G)
  outside_degree_one : ∀v∉lowVertices G,(M⊔edge w b).degree v≤1
  left_arm_mem : a∈outerLeaves (M⊔edge w b) (lowVertices G)
  right_arm_mem : b∈outerLeaves (M⊔edge w b) (lowVertices G)
  arms_ne : a≠b
  low_subset : lowVertices G⊆U
  projection : Projection G (outerLeaves (M⊔edge w b) (lowVertices G)) U
    (nonisolatedVertices (M⊔edge w b))
  h : ℕ
  positive : 2≤h
  count_le : h≤k
  e : (Fin h×Bool)≃ outerLeaves (M⊔edge w b) (lowVertices G)
  separated : (e.symm ⟨a,left_arm_mem⟩).1≠(e.symm ⟨b,right_arm_mem⟩).1
  paths : ∀i,G.Walk (projection.representative (e (i,false))).val
    (projection.representative (e (i,true))).val
  paths_simple : ∀i,(paths i).IsPath
  paths_disjoint : ∀i j,i≠j → ∀v,v∈(paths i).support → v∉(paths j).support
  paths_cover : ∀v,v∉U → ∃i,v∈(paths i).support
  paths_off : ∀i,∀v∈(paths i).support,v∉U
  paths_avoid : ∀i,∀z t,(PathGraphRealization.pathGraph (paths i)).Adj z t →
    ¬((M⊔edge w b)⊔projection.matching).Adj z t
  left_arm_on_path : (projection.representative ⟨a,left_arm_mem⟩).val∈
    (paths (e.symm ⟨a,left_arm_mem⟩).1).support
  right_arm_on_path : (projection.representative ⟨b,right_arm_mem⟩).val∈
    (paths (e.symm ⟨b,right_arm_mem⟩).1).support
  attachment_core_degree : ∀v,v∉U → ((M⊔edge w b)⊔projection.matching).degree v=
    if ∃a : outerLeaves (M⊔edge w b) (lowVertices G),(projection.representative a).val=v then 1 else 0

/-- G1, matching selection, projection and dense path extension are all
discharged here. The order threshold is chosen before the vertex type. -/
theorem above_half_odd_core_path_preparation (ε : ℝ) (hε : 0<ε) :
    ∃q : ℕ,2≤q ∧ ∃N : ℕ,
      ∀{V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        N≤Fintype.card V → Overfull.IsDeltaCritical G →
        ((1:ℝ)/2+ε)*(Fintype.card V:ℝ)≤(G.maxDegree:ℝ) →
        Odd (lowVertices G).card → 3≤(lowVertices G).card →
        let k:=Fintype.card V/(4096*q^2)
        let U:=exceptions G G.maxDegree (Fintype.card V/(8*q))
        U.card≤k ∧ Nonempty (OddPrepared G U k) := by
  obtain ⟨q,hq,N,htrim⟩:=
    CriticalDenseCoreTrimming.above_half_critical_sparse_trimming.{u} ε hε
  refine ⟨q,hq,max N (2*4096*q^2),?_⟩
  intro V _ _ G _ hn hc hdense hodd hthree
  let n:=Fintype.card V
  let a:=n/(8*q)
  let k:=n/(4096*q^2)
  let W:=lowVertices G
  let U:=exceptions G G.maxDegree a
  obtain ⟨_,hUk,htr⟩:=htrim G ((le_max_left _ _).trans hn) hc hdense
  change U.card≤k at hUk
  change U.card≤k ∧ Nonempty (OddPrepared G U k)
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
  obtain ⟨M,w,aa,bb,hMG,hm,hcover,hcrossM,hw,hmwa,hbb,hfresh,hextra,hs,hout,haA,hbA,hab,hA4⟩:=
    OddLowSkeletonWitness.exists_odd_low_skeleton G hc hthree hodd
  let H:=M⊔edge w bb
  let A:=outerLeaves H W
  let Z:=nonisolatedVertices H
  have hA : A.card≤W.card+1 := hs.outer_card_le
  have hZ : Z.card≤2*(W.card+1) :=
    (nonisolatedVertices_card_le_twice_edges H).trans (Nat.mul_le_mul_left 2 hs.edge_bound)
  obtain ⟨P⟩:=CriticalLowPartnerProjection.exists_projection_avoiding_of_low_partners
    G hc a k hD haD hscale hUk A Z hA hZ (fun x hx => hs.outer_neighbour hx)
  let Q:=H⊔P.matching
  have hQG : Q≤G := LowSkeletonAttachmentDegrees.attachment_le hs.le_graph P
  have hQ : Q.maxDegree≤2 := Q.maxDegree_le_of_forall_degree_le 2
    (LowSkeletonAttachmentDegrees.degree_le_two hWU hs.crosses hs.degree_le_two hout P)
  let armA : A:=⟨aa,haA⟩
  let armB : A:=⟨bb,hbA⟩
  have hArm : armA≠armB := fun he => hab (congrArg Subtype.val he)
  obtain ⟨h,hh,e,hsep⟩:=PairedEndpointEnumeration.exists_pairing_separating A hs.outer_even hA4 armA armB hArm
  have hAh : A.card=2*h := by
    have he:=Fintype.card_congr e
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe] at he
    omega
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
  have harm : ∀x:A,(P.representative x).val∈(ambient (e.symm x).1).support := by
    intro x
    obtain ⟨⟨i,b⟩,rfl⟩:=e.surjective x
    cases b
    · have hi : (e.symm (e (i,false))).1=i := congrArg Prod.fst (e.symm_apply_apply (i,false))
      rw [hi]
      exact (ambient i).start_mem_support
    · have hi : (e.symm (e (i,true))).1=i := congrArg Prod.fst (e.symm_apply_apply (i,true))
      rw [hi]
      exact (ambient i).end_mem_support
  exact ⟨{
    M:=M,w:=w,a:=aa,b:=bb,base_le:=hMG,base_matching:=hm,base_cover:=hcover,base_cross:=hcrossM,
    w_low:=hw,matched_arm:=hmwa,fresh_outside:=hbb,fresh_degree_zero:=hfresh,extra_arm:=hextra,
    skeleton:=hs,outside_degree_one:=hout,left_arm_mem:=haA,right_arm_mem:=hbA,arms_ne:=hab,
    low_subset:=hWU,projection:=P,h:=t+1,positive:=hh,count_le:=hhk,e:=e,separated:=hsep,
    paths:=ambient,paths_simple:=has,paths_disjoint:=had,paths_cover:=hco,paths_off:=hoff,paths_avoid:=havoid,
    left_arm_on_path:=harm armA,right_arm_on_path:=harm armB,
    attachment_core_degree:=fun v hv =>
      LowSkeletonAttachmentDegrees.degree_on_core hWU hs.crosses hout P hv }⟩

end OverfullWork.CriticalOddCorePathPreparation
