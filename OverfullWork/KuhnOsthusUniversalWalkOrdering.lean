module

public import OverfullWork.KuhnOsthusUniversalChordCounts
public import OverfullWork.MergeConnectedCycles
public import OverfullWork.SuccessorSwitchOrbits

@[expose] public section


/-! Order the labeled arc occurrences of a regular multidigraph by
joining the cycles through the distinguished base Hamilton cycle
in Kühn–Osthus Lemma 9.1. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedPrefactor
open scoped Classical
variable {E I : Type*} [Fintype E]

/-- An alignment of incoming and outgoing arc occurrences can be
made into one cyclic ordering whenever its distinguished orbit already
visits every source label. Equal labels are the only swaps used. -/
theorem exists_single_orbit_arc_alignment (src dst : E → I) (root : E)
    (σ : Equiv.Perm E) (hσ : ∀ e, src (σ e) = dst e)
    (hRoot : ∀ e, ∃ f, σ.SameCycle root f ∧ src f = src e) :
    ∃ ρ : Equiv.Perm E, (∀ e, src (ρ e) = dst e) ∧ ∀ e, ρ.SameCycle root e := by
  let P := (univ : Finset (Equiv.Perm E)).filter fun p =>
    (∀ e, src (p e) = dst e) ∧ ∀ e, ∃ f, p.SameCycle root f ∧ src f = src e
  have hNon : P.Nonempty := ⟨σ,mem_filter.mpr ⟨mem_univ _,hσ,hRoot⟩⟩
  obtain ⟨p,hp,hMax⟩ := exists_max_image P (fun p => (orbit p root).card) hNon
  obtain ⟨hP,hHit⟩ := (mem_filter.mp hp).2
  refine ⟨p,hP,?_⟩
  intro a
  by_contra ha
  obtain ⟨b,hb,hLabel⟩ := hHit a
  have hUnrelated : ¬ p.SameCycle a b := fun hab => ha (hb.trans hab.symm)
  let p' := Equiv.swap a b * p
  obtain ⟨hab,hOld⟩ := sameCycle_merge_of_left_swap p a b hUnrelated
  have hSrcSwap (e : E) : src (Equiv.swap a b e) = src e := by
    by_cases h₁ : e = a
    · subst e
      simpa using hLabel
    by_cases h₂ : e = b
    · subst e
      simpa using hLabel.symm
    rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  have hNew : p' ∈ P := mem_filter.mpr ⟨mem_univ _,fun e =>
    (hSrcSwap (p e)).trans (hP e),fun e => by
      obtain ⟨f,hf,he⟩ := hHit e
      exact ⟨f,hOld _ _ hf,he⟩⟩
  have hSub : orbit p root ⊂ orbit p' root := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨fun e he =>
      (orbit_mem_iff _ _ _).mpr (hOld _ _ ((orbit_mem_iff _ _ _).mp he)),?_⟩
    intro he
    have hmem : a ∈ orbit p' root := (orbit_mem_iff _ _ _).mpr ((hOld _ _ hb).trans hab.symm)
    exact ha ((orbit_mem_iff _ _ _).mp (he ▸ hmem))
  exact (not_le_of_gt (card_lt_card hSub)) (hMax p' hNew)

/-- Lemma 9.1 with explicit integer routing budgets. Each occurrence
of a chord is counted separately and the remaining arcs are exactly
the padding and one distinguished copy of the base cycle. -/
theorem exists_universal_walk_of_chord_budgets [Fintype I]
    (R : Digraph I) (s : Equiv.Perm I) (x₀ : I)
    (r g t cap budget L : ℕ)
    (hBase : ∀ x, s.SameCycle x₀ x) (hs : ∀ x, R.Adj x (s x))
    (hRobust : IsRobustAt R r t) (hg : 0 < g) (hAvoid : 2*budget+g ≤ r)
    (hOut : ∀ i, t+2*budget ≤ outDegree R i) (hIn : ∀ i, t ≤ inDegree R i)
    (hMass : Fintype.card I * (2*(Fintype.card I/g+3)) < cap*(budget+1))
    (hL : cap+4 ≤ L) :
    ∃ l : I → List I, ∃ F : Fin (L+1) → Equiv.Perm I,
      (∀ j, DirectedListRoutes.Route (reindexSources R s.symm) j (s j) (l j) ∧
        (l j).length ≤ Fintype.card I/g+3) ∧
      F 0 = s ∧ (∀ j x, R.Adj x (F j x)) ∧
      (∀ x y, ((univ : Finset (Fin (L+1))).filter (fun j => F j x = y)).card =
        elementaryChordMultiplicity s l x y +
          if s x = y then L+1 - (∑ z, elementaryChordMultiplicity s l x z) else 0) ∧
      HasSpanningCycle (fun e f : (Σ _ : Fin (L+1), I) => F e.1 e.2 = f.2) := by
  obtain ⟨l,hRoutes,hBound⟩ := exists_chord_routes_with_bounded_interior_load R s
    (fun j : I => j) s r g t cap budget hRobust hg hAvoid (fun i => hOut (s.symm i))
    (fun i => hIn (s i)) hMass
  have hCap (x : I) : (∑ j, (chordSources s j (l j)).count x) ≤ L := by
    have h := sum_le_sum (s := (univ : Finset I))
      (fun j _ => chord_endpoint_load_le R s j (s j) (l j) (hRoutes j).1 x)
    simp only [sum_add_distrib,s.symm_apply_eq,←s.eq_symm_apply,sum_ite_eq',mem_univ,if_true] at h
    have h' := hBound x
    omega
  obtain ⟨F,hF,hRow,hCol,hMult⟩ :=
    exists_padded_chord_factorization R s l L hs (fun i => (hRoutes i).1) hCap
  let J := Fin (L+1)
  let F' (j : J) := Fin.cases (motive := fun _ => Equiv.Perm I) s F j
  have hMult' (x y : I) : ((univ : Finset J).filter (fun j => F' j x = y)).card =
      elementaryChordMultiplicity s l x y +
        if s x = y then L+1 - (∑ z, elementaryChordMultiplicity s l x z) else 0 := by
    have hCount : ((univ : Finset J).filter (fun j => F' j x = y)).card =
        (if s x = y then 1 else 0) + ((univ : Finset (Fin L)).filter (fun j => F j x = y)).card := by
      rw [card_filter,Fin.sum_univ_succ,card_filter]
      rfl
    rw [hCount,hMult]
    have hN : (∑ z, elementaryChordMultiplicity s l x z) ≤ L := (hRow x).trans_le (hCap x)
    split_ifs <;> omega
  refine ⟨l,F',fun j => ⟨(hRoutes j).1,(hRoutes j).2.2⟩,rfl,?_,hMult',?_⟩
  · intro j
    exact Fin.cases (motive := fun j => ∀ x, R.Adj x (F' j x)) hs hF j
  · let E := Σ _ : J, I
    let π : Equiv.Perm E := Equiv.sigmaCongrRight F'
    let a₀ : E := ⟨0,x₀⟩
    let src (e : E) := e.2
    let dst (e : E) := F' e.1 e.2
    have hπ (e : E) : src (π e) = dst e := rfl
    have hBaseπ (x : I) : π.SameCycle a₀ (⟨0,x⟩ : E) := by
      obtain ⟨n,_,hn⟩ := (hBase x).exists_pow_eq'
      rw [Equiv.Perm.coe_pow] at hn
      have hIter (k : ℕ) : (π : E → E)^[k] a₀ = (⟨0,(s : I → I)^[k] x₀⟩ : E) := by
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [iterate_succ_apply',ih,iterate_succ_apply']
          rfl
      have h := successor_sameCycle_iterate π a₀ n
      rwa [hIter,hn] at h
    obtain ⟨ρ,hρ,hAll⟩ :=
      exists_single_orbit_arc_alignment src dst a₀ π hπ (fun e => ⟨⟨0,e.2⟩,hBaseπ _,rfl⟩)
    obtain ⟨walk,x,hDistinct,hCover,hHead,hChain⟩ := spanning_cycle_of_single_orbit ρ a₀ hAll
    refine ⟨walk,x,hDistinct,hCover,hHead,hChain.imp ?_⟩
    intro e f h
    exact ((congrArg src h).symm.trans (hρ e)).symm

private noncomputable def labelFiber {A J : Type*} [Fintype A] (f : A → J) (j : J) : Finset A :=
  univ.filter (fun a => f a = j)

private theorem mem_labelFiber {A J : Type*} [Fintype A] (f : A → J) (j : J) (a : A) :
    a ∈ labelFiber f j ↔ f a = j := by simp [labelFiber]

private theorem embedding_by_fibers {A B J : Type*} [Fintype A] [Fintype B]
    (f : A → J) (g : B → J)
    (h : ∀ j, (labelFiber f j).card ≤ (labelFiber g j).card) :
    ∃ e : A ↪ B, (∀ a, g (e a) = f a) ∧
      ∀ j, (labelFiber f j).card = (labelFiber g j).card →
        ∀ b, g b = j → ∃ a, e a = b := by
  classical
  let E (j : J) : ↥(labelFiber f j) ↪ ↥(labelFiber g j) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using h j))
  let p (j : J) : {a // f a = j} ≃ ↥(labelFiber f j) :=
    ⟨fun a => ⟨a.val,(mem_labelFiber f j a.val).mpr a.prop⟩,
      fun a => ⟨a.val,(mem_labelFiber f j a.val).mp a.prop⟩,fun _ => rfl,fun _ => rfl⟩
  let q (j : J) : ↥(labelFiber g j) ≃ {b // g b = j} :=
    ⟨fun b => ⟨b.val,(mem_labelFiber g j b.val).mp b.prop⟩,
      fun b => ⟨b.val,(mem_labelFiber g j b.val).mpr b.prop⟩,fun _ => rfl,fun _ => rfl⟩
  let K := Function.Embedding.sigmaMap (β := fun j => {a // f a = j})
    (β' := fun j => {b // g b = j}) (Function.Embedding.refl J)
    (fun j => (p j).toEmbedding.trans ((E j).trans (q j).toEmbedding))
  let e := (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans
    (K.trans (Equiv.sigmaFiberEquiv g).toEmbedding)
  have hE (a : A) : g (e a) = f a := (q (f a) (E (f a) (p (f a) ⟨a,rfl⟩))).prop
  refine ⟨e,hE,?_⟩
  intro j hj b hb
  have hSurj := (Fintype.bijective_iff_injective_and_card (E j)).mpr
    ⟨(E j).injective,by simpa only [Fintype.card_coe] using hj⟩
  obtain ⟨a,ha⟩ := hSurj.2 ((q j).symm ⟨b,hb⟩)
  refine ⟨(Equiv.sigmaFiberEquiv f) ⟨j,(p j).symm a⟩,?_⟩
  change (Equiv.sigmaFiberEquiv g) (K ((Equiv.sigmaFiberEquiv f).symm
    ((Equiv.sigmaFiberEquiv f) ⟨j,(p j).symm a⟩))) = b
  rw [Equiv.symm_apply_apply]
  change (q j (E j (p j ((p j).symm a)))).val = b
  rw [Equiv.apply_symm_apply,ha,Equiv.apply_symm_apply]

/-- Identify each elementary chord with a different occurrence in the
universal walk. All unassigned occurrences are edges of the base cycle. -/
theorem exists_universal_chord_occurrence_embedding [Fintype I]
    (s : Equiv.Perm I) (l : I → List I) {L : ℕ} (F : Fin L → Equiv.Perm I)
    (hMult : ∀ x y, ((univ : Finset (Fin L)).filter (fun j => F j x = y)).card =
      elementaryChordMultiplicity s l x y +
        if s x = y then L - (∑ z, elementaryChordMultiplicity s l x z) else 0) :
    let P := Σ j, Fin (l j).length
    let src (p : P) := s.symm ((p.1 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt))
    let dst (p : P) := (l p.1)[p.2.val]
    ∃ e : P ↪ (Fin L × I),
      (∀ p, (e p).2 = src p ∧ F (e p).1 (e p).2 = dst p) ∧
      ∀ j x, F j x ≠ s x → ∃ p, e p = (j,x) := by
  intro P src dst
  let f (p : P) := (src p,dst p)
  let g (v : Fin L × I) := (v.2,F v.1 v.2)
  have hA (x y : I) : (labelFiber f (x,y)).card =
      elementaryChordMultiplicity s l x y := by
    unfold labelFiber elementaryChordMultiplicity
    congr 1
    ext p
    simp only [f,mem_filter,Prod.mk.injEq,src,dst]
  have hB (x y : I) : (labelFiber g (x,y)).card =
      ((univ : Finset (Fin L)).filter (fun j => F j x = y)).card := by
    apply card_bij (fun v _ => v.1)
    · intro v hv
      obtain ⟨hV,hxy⟩ := (Prod.mk.injEq ..).mp ((mem_labelFiber g (x,y) v).mp hv)
      exact mem_filter.mpr ⟨mem_univ _,hV ▸ hxy⟩
    · intro a ha b hb he
      have ha' := ((Prod.mk.injEq ..).mp ((mem_labelFiber g (x,y) a).mp ha)).1
      have hb' := ((Prod.mk.injEq ..).mp ((mem_labelFiber g (x,y) b).mp hb)).1
      exact Prod.ext he (ha'.trans hb'.symm)
    · intro j hj
      exact ⟨(j,x),(mem_labelFiber g (x,y) (j,x)).mpr (Prod.ext rfl (mem_filter.mp hj).2),rfl⟩
  obtain ⟨e,he,hCover⟩ := embedding_by_fibers f g (fun ⟨x,y⟩ => by
    rw [hA,hB,hMult]
    exact Nat.le_add_right ..)
  refine ⟨e,fun p => (Prod.mk.injEq ..).mp (he p),?_⟩
  intro j x h
  apply hCover (x,F j x) _ (j,x) rfl
  rw [hA,hB,hMult,if_neg h.symm,add_zero]

end OverfullWork.DirectedRobustExpansion
