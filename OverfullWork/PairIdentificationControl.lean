module

public import OverfullWork.PairIdentification

@[expose] public section


namespace OverfullWork.PairIdentification
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

private theorem fibre_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (e : Sym2 (Vertices v)) (A : Finset (Sym2 V))
    (hA : ∀a∈EdgeImage.fibre G (vertexMap u v huv) e,a.val∈A) :
    (EdgeImage.fibre G (vertexMap u v huv) e).card≤A.card := by
  have hsub : (EdgeImage.fibre G (vertexMap u v huv) e).image Subtype.val⊆A := by
    intro z hz
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hz
    exact hA a ha
  have h:=card_le_card hsub
  rwa [card_image_of_injective _ Subtype.val_injective] at h

/-- No parallel edges are created away from the retained vertex. -/
theorem isStarAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) :
    (graph G u v huv hnon).IsStarAt (centre u v huv) := by
  intro a b ha hb
  have hau : a.val≠u := fun h => ha (Subtype.ext h)
  have hbu : b.val≠u := fun h => hb (Subtype.ext h)
  change (EdgeImage.fibre G (vertexMap u v huv) s(a,b)).card≤1
  have hh:=fibre_card_le G u v huv s(a,b) {s(a.val,b.val)} (by
    intro e he
    let p:=MultiGraph.GeneralCopies.endpoints e.val
    have hp : s(p.1,p.2)=e.val:=MultiGraph.GeneralCopies.endpoints_eq e.val
    have hm : s(vertexMap u v huv p.1,vertexMap u v huv p.2)=s(a,b) := by
      rw [←Sym2.map_mk,hp]
      exact (mem_filter.mp he).2
    rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
    · have h1':= (map_eq_other u v huv p.1 a hau).mp h1
      have h2':= (map_eq_other u v huv p.2 b hbu).mp h2
      simpa only [mem_singleton,h1',h2'] using hp.symm
    · have h1':= (map_eq_other u v huv p.1 b hbu).mp h1
      have h2':= (map_eq_other u v huv p.2 a hau).mp h2
      apply mem_singleton.mpr
      rw [←hp,h1',h2',Sym2.eq_swap])
  simpa using hh

/-- Each surviving vertex can receive at most the two edges from u and v. -/
theorem centre_mult_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) (b : Vertices v) :
    (graph G u v huv hnon).mult s(centre u v huv,b)≤2 := by
  by_cases hb : b=centre u v huv
  · rw [hb,(graph G u v huv hnon).loopless _ (by simp)]
    omega
  have hbu : b.val≠u := fun h => hb (Subtype.ext h)
  change (EdgeImage.fibre G (vertexMap u v huv) s(centre u v huv,b)).card≤2
  apply (fibre_card_le G u v huv _ {s(u,b.val),s(v,b.val)} ?_).trans
    (by have hh:=card_insert_le s(u,b.val) {s(v,b.val)};simpa using hh)
  intro e he
  let p:=MultiGraph.GeneralCopies.endpoints e.val
  have hp : s(p.1,p.2)=e.val:=MultiGraph.GeneralCopies.endpoints_eq e.val
  have hm : s(vertexMap u v huv p.1,vertexMap u v huv p.2)=s(centre u v huv,b) := by
    rw [←Sym2.map_mk,hp]
    exact (mem_filter.mp he).2
  rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
  · have h1':= (map_eq_centre u v huv p.1).mp h1
    have h2':= (map_eq_other u v huv p.2 b hbu).mp h2
    rw [←hp,h2']
    rcases h1' with h|h <;> simp [h]
  · have h1':= (map_eq_other u v huv p.1 b hbu).mp h1
    have h2':= (map_eq_centre u v huv p.2).mp h2
    rw [←hp,h1',Sym2.eq_swap]
    rcases h2' with h|h <;> simp [h]

theorem multiplicity_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) :
    ∀e,(graph G u v huv hnon).mult e≤2 := by
  intro e
  induction e using Sym2.inductionOn with
  | hf a b =>
    by_cases ha : a=centre u v huv
    · subst a;exact centre_mult_le_two G u v huv hnon b
    by_cases hb : b=centre u v huv
    · subst b;rw [Sym2.eq_swap];exact centre_mult_le_two G u v huv hnon a
    exact (isStarAt G u v huv hnon a b ha hb).trans (by omega)

theorem parallelBudget (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) :
    (graph G u v huv hnon).HasParallelBudget (centre u v huv) 2 := by
  intro a ha
  have hp : ∀b,(graph G u v huv hnon).mult s(a,b)-1≤ if b=centre u v huv then 1 else 0 := by
    intro b
    by_cases hb : b=centre u v huv
    · rw [if_pos hb];have hh:=multiplicity_le_two G u v huv hnon s(a,b);omega
    · rw [if_neg hb];have hh:=isStarAt G u v huv hnon a b ha hb;omega
  have hh:=sum_le_sum (s:=univ) (fun b _=>hp b)
  have hs : (∑b : Vertices v,if b=centre u v huv then 1 else 0)=1 := by simp
  rw [hs] at hh
  exact hh.trans (by omega)

theorem centreControl (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u≠v) (hnon : ¬G.Adj u v) :
    (graph G u v huv hnon).CentreControl (centre u v huv) 2 :=
  Or.inl (centre_mult_le_two G u v huv hnon)

end OverfullWork.PairIdentification
