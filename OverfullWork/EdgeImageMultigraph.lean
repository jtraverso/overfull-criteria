module

public import OverfullWork.SimpleColouringBridge
public import OverfullWork.MultigraphColouring

@[expose] public section


/-! # A genuine vertex identification multigraph

Every original edge remains a distinct labelled copy. Multiplicities in the
image are defined by their actual fibres. The colouring pullback assigns
distinct available colours to the edges in each fibre, rather than assuming
an edge embedding or identifying independently chosen colourings.
-/
namespace OverfullWork.EdgeImage
open SimpleGraph Finset
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
set_option maxHeartbeats 5000000

def fibre (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → W) (e : Sym2 W) : Finset G.edgeSet :=
  univ.filter fun a => Sym2.map f a.val=e

/-- The multiplicity is the number of original edges identified with e. -/
noncomputable def graph (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → W)
    (hloop : ∀u v,G.Adj u v → f u≠f v) : MultiGraph W where
  mult e := (fibre G f e).card
  loopless e he := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hmap := (mem_filter.mp ha).2
    let p:=MultiGraph.GeneralCopies.endpoints a.val
    have hp : s(p.1,p.2)=a.val:=MultiGraph.GeneralCopies.endpoints_eq a.val
    have hadj : G.Adj p.1 p.2 := by
      apply (mem_edgeSet G).mp
      rw [hp]
      exact a.property
    have hd : (s(f p.1,f p.2)).IsDiag := by
      rw [←Sym2.map_mk,hp,hmap]
      exact he
    exact hloop p.1 p.2 hadj (Sym2.mk_isDiag_iff.mp hd)

theorem degree_eq (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → W)
    (hloop : ∀u v,G.Adj u v → f u≠f v) (w : W) :
    (graph G f hloop).degree w=(univ.filter fun a : G.edgeSet => w∈Sym2.map f a.val).card := by
  change (∑e∈univ.filter (fun e : Sym2 W => w∈e),(fibre G f e).card)=_
  unfold fibre
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  ext a
  simp

private theorem colour_le_one {M : MultiGraph W} {D : ℕ} (C : M.EdgeColoring D)
    (e : Sym2 W) (i : Fin D) : C.col e i≤1 := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hs:=single_le_sum (s:=univ.filter fun e : Sym2 W => a∈e)
      (f:=fun e => C.col e i) (fun _ _ => Nat.zero_le _)
      (mem_filter.mpr ⟨mem_univ _,by simp⟩ : s(a,b)∈univ.filter fun e : Sym2 W => a∈e)
    exact hs.trans (C.proper a i)

private theorem used_card {M : MultiGraph W} {D : ℕ} (C : M.EdgeColoring D) (e : Sym2 W) :
    (univ.filter fun i => C.col e i=1).card=M.mult e := by
  rw [card_eq_sum_ones,sum_filter]
  calc
    _ = ∑i : Fin D,C.col e i := by
      apply sum_congr rfl
      intro i _
      have hh:=colour_le_one C e i
      split_ifs <;> omega
    _ = _ := C.sum_col e

omit [DecidableEq V] in
/-- Pull back an actual colouring of the identified multigraph. Parallel
copies in each image fibre receive different colours by a constructed
finite equivalence. -/
theorem colourable_of_image_colouring (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → W)
    (hloop : ∀u v,G.Adj u v → f u≠f v) {D : ℕ}
    (C : (graph G f hloop).EdgeColoring D) : G.EdgeColorable D := by
  let M:=graph G f hloop
  let used := fun e : Sym2 W => univ.filter fun i => C.col e i=1
  have hcard : ∀e : Sym2 W,Fintype.card ↥(fibre G f e)=Fintype.card ↥(used e) := by
    intro e
    simp only [Fintype.card_coe]
    exact (used_card C e).symm
  let equiv := fun e : Sym2 W => Fintype.equivOfCardEq (hcard e)
  let lift := fun a : G.edgeSet => equiv (Sym2.map f a.val)
    ⟨a,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  let col := fun a : G.edgeSet => (lift a).val
  have hpositive : ∀a : G.edgeSet,C.col (Sym2.map f a.val) (col a)=1 := by
    intro a
    exact (mem_filter.mp (lift a).property).2
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro a b hab heq
  rw [lineGraph_adj_iff_exists] at hab
  obtain ⟨hne,v,hva,hvb⟩:=hab
  have hma : f v∈Sym2.map f a.val:=Sym2.mem_map.mpr ⟨v,hva,rfl⟩
  have hmb : f v∈Sym2.map f b.val:=Sym2.mem_map.mpr ⟨v,hvb,rfl⟩
  have hea := hpositive a
  have heb := hpositive b
  have hpa : 0<C.col (Sym2.map f a.val) (col a) := by rw [hea];norm_num
  have hpb : 0<C.col (Sym2.map f b.val) (col a) := by rw [heq,heb];norm_num
  have himg : Sym2.map f a.val=Sym2.map f b.val :=
    C.eq_of_incident_positive hma hmb hpa hpb
  have hba : b∈fibre G f (Sym2.map f a.val) :=
    mem_filter.mpr ⟨mem_univ _,himg.symm⟩
  have hca : (equiv (Sym2.map f a.val) ⟨a,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩).val=col a:=rfl
  have transport (e e' : Sym2 W) (hee : e=e') (b : G.edgeSet)
      (hb : b∈fibre G f e) (hb' : b∈fibre G f e') :
      (equiv e ⟨b,hb⟩).val=(equiv e' ⟨b,hb'⟩).val := by
    subst e'
    rfl
  have hcb : (equiv (Sym2.map f a.val) ⟨b,hba⟩).val=col b := by
    exact transport _ _ himg b hba (mem_filter.mpr ⟨mem_univ _,rfl⟩)
  have hsame : equiv (Sym2.map f a.val) ⟨a,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩=
      equiv (Sym2.map f a.val) ⟨b,hba⟩ := Subtype.ext (hca.trans (heq.trans hcb.symm))
  exact hne (congrArg Subtype.val ((equiv (Sym2.map f a.val)).injective hsame))

end OverfullWork.EdgeImage
