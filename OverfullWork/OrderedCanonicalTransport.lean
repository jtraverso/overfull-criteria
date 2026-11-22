module

public import OverfullWork.CanonicalNoOverfullCompletion
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section


/-! # Constructed degree ordering and canonical completion on any even type

The coordinates are obtained by sorting a finite tuple of actual
degrees.  Reindexing preserves the multigraph's degrees and all internal
edge counts, so the no-overfull input transports to the ordered graph.
The endpoint constructs a canonical completion, without claiming a
factorization of that completion.
-/
namespace OverfullWork.OrderedCanonicalTransport
open SimpleGraph Finset
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
set_option maxHeartbeats 4000000

/-- Pull back the actual multiplicity function along a vertex equivalence. -/
def reindex (M : MultiGraph V) (e : W ≃ V) : MultiGraph W where
  mult a := M.mult (Sym2.map e a)
  loopless a ha := M.loopless (Sym2.map e a) ha.map

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem reindex_mult (M : MultiGraph V) (e : W ≃ V) (a : Sym2 W) :
    (reindex M e).mult a=M.mult (Sym2.map e a) := rfl

theorem degree_reindex (M : MultiGraph V) (e : W ≃ V) (w : W) :
    (reindex M e).degree w=M.degree (e w) := by
  rw [MultiGraph.degree_eq_sum_mult,MultiGraph.degree_eq_sum_mult]
  change (∑ z : W,M.mult s(e w,e z))=∑ v : V,M.mult s(e w,v)
  exact e.sum_comp (fun v => M.mult s(e w,v))

omit [Fintype V] [Fintype W] [DecidableEq W] in
theorem twiceInternal_reindex (M : MultiGraph V) (e : W ≃ V) (S : Finset W) :
    (reindex M e).twiceInternal S=M.twiceInternal (S.image e) := by
  unfold MultiGraph.twiceInternal
  rw [sum_image (fun a _ b _ h => e.injective h)]
  apply sum_congr rfl
  intro u hu
  rw [sum_image (fun a _ b _ h => e.injective h)]
  rfl

theorem edgesWithin_reindex (M : MultiGraph V) (e : W ≃ V) (S : Finset W) :
    (reindex M e).edgesWithin S=M.edgesWithin (S.image e) := by
  have h := twiceInternal_reindex M e S
  rw [MultiGraph.twiceInternal_eq,MultiGraph.twiceInternal_eq] at h
  omega

theorem no_overfull_reindex (M : MultiGraph V) (e : W ≃ V) (D : ℕ)
    (hno : ¬M.HasOverfullSubset D) : ¬(reindex M e).HasOverfullSubset D := by
  rintro ⟨S,hS⟩
  apply hno
  refine ⟨S.image e,?_⟩
  rw [card_image_of_injective _ e.injective,←edgesWithin_reindex M e S]
  exact hS

/-- Consecutive pair coordinates: false has rank 2i, true rank 2i+1. -/
def pairedIndex (m : ℕ) : (Fin m×Bool) ≃ Fin (2*m) where
  toFun z := ⟨2*z.1.val+(if z.2 then 1 else 0),by
    cases z.2 with
    | false => simp only [Bool.false_eq_true,↓reduceIte]; omega
    | true => simp only [↓reduceIte]; omega⟩
  invFun i := (⟨i.val/2,by omega⟩,decide (i.val%2=1))
  left_inv z := by
    obtain ⟨i,b⟩ := z
    cases b <;> apply Prod.ext
    · apply Fin.ext
      simp only [Bool.false_eq_true,↓reduceIte]
      omega
    · simp
    · apply Fin.ext
      simp only [↓reduceIte]
      omega
    · simp
  right_inv i := by
    apply Fin.ext
    change 2*(i.val/2)+(if decide (i.val%2=1) then 1 else 0)=i.val
    by_cases hmod : i.val%2=1 <;> simp_all <;> omega

theorem pairedIndex_false_val (m : ℕ) (i : Fin m) :
    (pairedIndex m (i,false)).val=2*i.val := by simp [pairedIndex]

theorem pairedIndex_true_val (m : ℕ) (i : Fin m) :
    (pairedIndex m (i,true)).val=2*i.val+1 := by simp [pairedIndex]

omit [DecidableEq V] in
/-- Sort an arbitrary natural-valued profile, with repeated values
handled by the library's genuine sorting permutation. -/
theorem exists_paired_sorted_equiv (f : V → ℕ) (m : ℕ)
    (hcard : Fintype.card V=2*m) :
    ∃ e : (Fin m×Bool) ≃ V,
      (∀ i : Fin m,f (e (i,false))≤f (e (i,true))) ∧
      ∀ i j : Fin m,i.val<j.val → f (e (i,true))≤f (e (j,false)) := by
  let e₀ : Fin (2*m) ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let profile : Fin (2*m) → ℕ := fun i => f (e₀ i)
  let e : (Fin m×Bool) ≃ V := (pairedIndex m).trans ((Tuple.sort profile).trans e₀)
  have hsorted := Tuple.monotone_sort profile
  refine ⟨e,?_,?_⟩
  · intro i
    apply hsorted
    change (pairedIndex m (i,false)).val≤(pairedIndex m (i,true)).val
    rw [pairedIndex_false_val,pairedIndex_true_val]
    omega
  · intro i j hij
    apply hsorted
    change (pairedIndex m (i,true)).val≤(pairedIndex m (j,false)).val
    rw [pairedIndex_false_val,pairedIndex_true_val]
    omega

/-- Construct the degree order and then the actual canonical completion
for an arbitrary finite even vertex type. -/
theorem exists_ordered_completion (M : MultiGraph V) (D n : ℕ)
    (hcard : Fintype.card V=2*(n+1)) (hD : ∀v,M.degree v≤D)
    (hno : ¬M.HasOverfullSubset D) :
    ∃ e : (Fin (n+1)×Bool) ≃ V,
      (∀i : Fin (n+1),M.degree (e (i,false))≤M.degree (e (i,true))) ∧
      (∀i j : Fin (n+1),i.val<j.val → M.degree (e (i,true))≤M.degree (e (j,false))) ∧
      Nonempty (CanonicalRegularization.Completion (reindex M e) D) := by
  obtain ⟨e,hpair,horder⟩ := exists_paired_sorted_equiv M.degree (n+1) hcard
  refine ⟨e,hpair,horder,?_⟩
  apply CanonicalNoOverfullCompletion.exists_completion_of_no_overfull
  · intro z
    rw [degree_reindex]
    exact hD (e z)
  · simpa only [degree_reindex] using hpair
  · simpa only [degree_reindex] using horder
  · exact no_overfull_reindex M e D hno

theorem exists_simple_ordered_completion (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card V=2*(n+1)) (hno : ¬G.HasOverfullSubgraph) :
    ∃ e : (Fin (n+1)×Bool) ≃ V,
      (∀i : Fin (n+1),G.degree (e (i,false))≤G.degree (e (i,true))) ∧
      (∀i j : Fin (n+1),i.val<j.val → G.degree (e (i,true))≤G.degree (e (j,false))) ∧
      Nonempty (CanonicalRegularization.Completion (reindex (MultiGraph.ofSimpleGraph G) e)
        G.maxDegree) := by
  have hD : ∀v,(MultiGraph.ofSimpleGraph G).degree v≤G.maxDegree := by
    intro v
    rw [MultiGraph.degree_ofSimpleGraph]
    exact G.degree_le_maxDegree v
  have hMno : ¬(MultiGraph.ofSimpleGraph G).HasOverfullSubset G.maxDegree := by
    rintro ⟨S,hS⟩
    rw [←OddCutDeficit.internalEdges_eq_multigraph] at hS
    exact hno ⟨S,hS⟩
  simpa only [MultiGraph.degree_ofSimpleGraph] using
    exists_ordered_completion (MultiGraph.ofSimpleGraph G) G.maxDegree n hcard hD hMno

end OverfullWork.OrderedCanonicalTransport
