module

public import OverfullWork.KuhnOsthusCompleteExceptionalCounts
public import OverfullWork.KuhnOsthusParityPacketProjection

@[expose] public section


/-! Use the original exceptional systems of Lemma 7.6 in the
closed interval cells required by the chord rounds. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V : Type*} [Fintype V]

/-- The canonical closed interval, including its terminal cluster,
has the support, local footprint and balance required in Lemma 9.7. -/
theorem winding_exceptional_interval_chord_bounds
    {f n m : ℕ} {G : Digraph V} (Z : Finset V)
    (X : Fin (f*(n+1)) → Finset ↥Zᶜ) (c : ↥Zᶜ → Fin (f*(n+1)))
    (hf : 2 ≤ f) (hLabel : ∀ j v, v ∈ X j → c v = j) (hSize : ∀ j, (X j).card = m)
    (i : Fin f) :
    letI : DecidableEq ↥Zᶜ := Classical.decEq _
    letI : DecidableEq (Fin (f*(n+1))) := Classical.decEq _
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let U (j : Fin f) := univ.biUnion (fun p : Fin (n+1) => X (intervalPosition j p))
    let S (j : Fin f) := X (intervalPosition j 0)
    ∀ P : OriginalInterval G Z
      ((U i).map e ∪ (S (finRotate f i)).map e) ((S i).map e) ((S (finRotate f i)).map e),
    let D := basicExceptionalPathSystem P.digraph Z
    finiteSatisfying (IncidentTo D) ⊆ U i ∪ U (finRotate f i) ∧
    (∀ x, (finiteSatisfying (fun v => c v = x ∧ IncidentTo D v)).card ≤ m) ∧
    ∀ x, (∑ p : Arc D, if c p.val.1 = x then (1:ℕ) else 0) =
      ∑ p : Arc D, if c p.val.2 = finRotate (f*(n+1)) x then (1:ℕ) else 0 := by
  classical
  intro e U S P D
  have hk : 0 < f*(n+1) := Nat.mul_pos (by omega) (by omega)
  have hLength : n+2 ≤ f*(n+1) := by
    have he := Nat.mul_le_mul_right (n+1) hf
    omega
  let b := (n+1)*i.val
  let loc (j : Fin (n+2)) : Fin (f*(n+1)) := ⟨(b+j.val)%(f*(n+1)),Nat.mod_lt _ hk⟩
  let T (j : Fin (n+2)) := X (loc j)
  have hLoc : Function.Injective loc := by
    intro j q he
    apply Fin.ext
    have hEq : b+j.val ≡ b+q.val [MOD f*(n+1)] := congrArg Fin.val he
    have hSub := Nat.ModEq.add_left_cancel' b hEq
    have hj : j.val < f*(n+1) := j.isLt.trans_le hLength
    have hq : q.val < f*(n+1) := q.isLt.trans_le hLength
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hq] using hSub
  have hStep (j : Fin (n+1)) : loc j.succ = finRotate (f*(n+1)) (loc j.castSucc) := by
    apply Fin.ext
    rw [finRotate_val_modulo]
    change (b+(j.val+1))%(f*(n+1)) = ((b+j.val)%(f*(n+1))+1)%(f*(n+1))
    rw [←Nat.add_assoc,Nat.mod_add_mod]
  let A := cyclicCluster (fun j => (X j).map e) hk
  have hGeom := winding_closed_interval_cells (fun j => (X j).map e) hk (by omega : 0 < n+1) i
  have hMap (i : Fin f) :
      (U i).map e = univ.biUnion (fun p : Fin (n+1) => (X (intervalPosition i p)).map e) := by
    ext v
    simp only [U,mem_map,mem_biUnion,mem_univ,true_and]
    exact ⟨fun ⟨a,⟨p,hp⟩,he⟩ => ⟨p,a,hp,he⟩,fun ⟨p,a,hp,he⟩ => ⟨a,⟨p,hp⟩,he⟩⟩
  have hFirst : (S i).map e = (T 0).map e := by
    apply hGeom.2.1.trans
    change (X ⟨b % (f*(n+1)),_⟩).map e = (X (loc 0)).map e
    simp only [loc,Fin.val_zero,Nat.add_zero]
  have hLast : (S (finRotate f i)).map e = (T (Fin.last (n+1))).map e := by
    apply hGeom.2.2.trans
    dsimp only [A,cyclicCluster,T,loc,b,Fin.val_last]
    rw [Nat.mul_succ (n+1) i.val]
  have hWhole : (U i).map e ∪ (S (finRotate f i)).map e = (univ.biUnion T).map e := by
    rw [hMap]
    refine hGeom.1.trans ?_
    ext v
    simp only [mem_clusterIntervalVertices,mem_map,mem_biUnion,mem_univ,true_and]
    rw [Nat.mul_succ]
    constructor
    · rintro ⟨j,hj,hj',hv⟩
      let p : Fin (n+2) := ⟨j-b,by dsimp [b]; omega⟩
      have he : b+p.val = j := by dsimp [p,b]; omega
      obtain ⟨a,ha,ha'⟩ := (mem_map.mp hv)
      exact ⟨a,⟨p,by simpa only [T,loc,A,cyclicCluster,he] using ha⟩,ha'⟩
    · rintro ⟨a,⟨p,hp⟩,rfl⟩
      refine ⟨b+p.val,by dsimp [b]; omega,by dsimp [b]; have := p.isLt; omega,?_⟩
      exact mem_map.mpr ⟨a,hp,rfl⟩
  let Q := P.castSets hWhole hFirst hLast
  letI : DecidableEq (Fin (f*(n+1))) := Classical.decEq _
  let HasCounts (R : Digraph V) :=
    let K := basicExceptionalPathSystem R Z
    (∀ x, (∑ p : Arc K, if c p.val.1 = x then (1:ℕ) else 0) =
      ∑ p : Arc K, if c p.val.2 = finRotate (f*(n+1)) x then (1:ℕ) else 0) ∧
    ∀ x, (finiteSatisfying (fun v => c v = x ∧ IncidentTo K v)).card ≤ m
  have hSame : Q.digraph = P.digraph := P.castSets_digraph hWhole hFirst hLast
  have hCounts : HasCounts Q.digraph := complete_exceptional_interval_arc_counts G Z c (finRotate _)
    loc T hLoc hStep (fun j v hv => hLabel _ v hv) (fun j => hSize _) Q
  have hCounts' : HasCounts P.digraph := hSame ▸ hCounts
  refine ⟨?_,hCounts'.2,hCounts'.1⟩
  · letI : DecidableEq ↥Zᶜ := Classical.decEq _
    intro v hv
    have hInc := (mem_finiteSatisfying (p := IncidentTo D)).mp hv
    have hSlots := basic_exceptional_endpoint_slots P.digraph Z P.cover
      (fun _ _ => P.no_internal) v
    have hArea : v.val ∈ (U i).map e ∪ (S (finRotate f i)).map e := by
      rcases hInc with hv | hv
      · exact (mem_sdiff.mp ((P.slots v.val (mem_compl.mp v.prop)).1.mp (hSlots.1.mp hv))).1
      · exact (mem_sdiff.mp ((P.slots v.val (mem_compl.mp v.prop)).2.mp (hSlots.2.mp hv))).1
    rcases mem_union.mp hArea with hu | hs
    · obtain ⟨a,ha,he⟩ := mem_map.mp hu
      exact mem_union_left _ (e.injective he ▸ ha)
    · obtain ⟨a,ha,he⟩ := mem_map.mp hs
      exact mem_union_right _ (mem_biUnion.mpr ⟨0,mem_univ _,e.injective he ▸ ha⟩)

end OverfullWork.DirectedRobustExpansion
