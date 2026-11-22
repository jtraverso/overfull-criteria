module

public import OverfullWork.OsthusStadenShadowPairDemand

@[expose] public section


/-! Choose the H2 batches for all physical cell pairs and all layers. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- A vertex lies on one side of at most one base cell. Its degree
across all pair batches is bounded by one batch cap per partner cell. -/
theorem batch_union_degree_le
    {U V : Type*} [Fintype U] [Fintype V]
    (base : U → Finset V) (C : U → U → Finset (V × V)) (S : Finset (V × V)) (cap : ℕ)
    (hBase : ∀ u v, u ≠ v → Disjoint (base u) (base v))
    (hEnds : ∀ u v e, e ∈ C u v → e.1 ∈ base u ∧ e.2 ∈ base v)
    (hCap : ∀ u v, (∀ x, ((C u v).filter (fun e => e.1 = x)).card ≤ cap) ∧
      ∀ x, ((C u v).filter (fun e => e.2 = x)).card ≤ cap)
    (hS : ∀ e ∈ S, ∃ u v, e ∈ C u v) (x : V) :
    inDegree (digraphOfArcs S) x ≤ Fintype.card U*cap ∧
      outDegree (digraphOfArcs S) x ≤ Fintype.card U*cap := by
  have hUnique (u v : U) (hu : x ∈ base u) (hv : x ∈ base v) : u = v :=
    Classical.byContradiction fun h => disjoint_left.mp (hBase u v h) hu hv
  have hCount (q : Bool) : (S.filter (fun e => (if q then e.1 else e.2) = x)).card ≤ Fintype.card U*cap := by
    by_cases hx : ∃ u, x ∈ base u
    · obtain ⟨u,hu⟩ := hx
      let B (v : U) := (if q then C u v else C v u).filter (fun e => (if q then e.1 else e.2) = x)
      have hSub : S.filter (fun e => (if q then e.1 else e.2) = x) ⊆ univ.biUnion B := by
        intro e he
        obtain ⟨he,hex⟩ := mem_filter.mp he
        obtain ⟨a,b,ha⟩ := hS e he
        obtain ⟨h1,h2⟩ := hEnds a b e ha
        cases q
        · have heq : e.2 = x := hex
          have hbu := hUnique b u (heq ▸ h2) hu
          subst b
          exact mem_biUnion.mpr ⟨a,mem_univ _,mem_filter.mpr ⟨ha,hex⟩⟩
        · have heq : e.1 = x := hex
          have hau := hUnique a u (heq ▸ h1) hu
          subst a
          exact mem_biUnion.mpr ⟨b,mem_univ _,mem_filter.mpr ⟨ha,hex⟩⟩
      have hBound (v : U) : (B v).card ≤ cap := by
        cases q
        · exact (hCap v u).2 x
        · exact (hCap u v).1 x
      calc
        _ ≤ (univ.biUnion B).card := card_le_card hSub
        _ ≤ ∑ v, (B v).card := card_biUnion_le
        _ ≤ ∑ _ : U, cap := sum_le_sum (fun v _ => hBound v)
        _ = _ := by simp
    · suffices hEmpty : S.filter (fun e => (if q then e.1 else e.2) = x) = ∅ by
        rw [hEmpty,card_empty]
        exact Nat.zero_le _
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hex⟩ := mem_filter.mp he
      obtain ⟨a,b,ha⟩ := hS e he
      obtain ⟨h1,h2⟩ := hEnds a b e ha
      cases q
      · exact hx ⟨b,(show e.2 = x from hex) ▸ h2⟩
      · exact hx ⟨a,(show e.1 = x from hex) ▸ h1⟩
  rw [digraphOfArcs_inDegree,digraphOfArcs_outDegree]
  exact ⟨hCount false,hCount true⟩

set_option maxHeartbeats 2250000 in
/-- Realize all supported shadow matrices simultaneously inside the
common reserve. Distinct pairs use disjoint base rectangles and
repeated uses of one rectangle are handled by the batch construction. -/
theorem exists_balancing_arcs_from_shared_reserve_pairs
    {L U V : Type*} [Fintype L] [Fintype U] [Fintype V]
    (factor : L → Equiv.Perm U) (incoming outgoing : L → Finset U)
    (label : L → V → Option U) (sin sout : L → U → ℕ)
    (Q : Digraph U) (reserve : Digraph V) (pair : U → U → Digraph V)
    (base : U → Finset V) (eligible : L → U → Finset V)
    (M : ∀ l, ↥(incoming l ∪ outgoing l) → ↥(incoming l ∪ outgoing l) → ℕ)
    (b c cap loss a used : ℕ) (ε d : ℝ)
    (hDis : ∀ l, Disjoint (incoming l) (outgoing l))
    (hSep : ∀ l u, u ∈ outgoing l → factor l u ∉ incoming l)
    (hIn : ∀ l u, u ∉ incoming l → sin l u = 0)
    (hOut : ∀ l u, u ∉ outgoing l → sout l u = 0)
    (hSupport : ∀ l v w, M l v w ≤ if Q.Adj
      (shadowSend (factor l) (incoming l) (outgoing l) v)
      (shadowReceive (factor l) (incoming l) (outgoing l) w) then b else 0)
    (hRow : ∀ l v, (∑ w,M l v w) = c+sin l v)
    (hCol : ∀ l w, (∑ v,M l v w) = c+sout l w)
    (hBase : ∀ u v, u ≠ v → Disjoint (base u) (base v))
    (hEligible : ∀ l u, eligible l u ⊆ base u)
    (hLabel : ∀ l u x, x ∈ eligible l u → label l x = some u)
    (hReserve : ∀ u v, pair u v ≤ reserve)
    (hRegular : ∀ u v, Q.Adj u v → IsUniform (pair u v) ε (base u) (base v) ∧
      d ≤ density (pair u v) (base u) (base v))
    (ha : 0 < a) (hcap : 0 < cap) (hLoss : b ≤ cap*loss)
    (hSize : ∀ l u, a+loss ≤ (eligible l u).card)
    (hLarge : ∀ u, ((base u).card:ℝ)*ε ≤ (a:ℝ))
    (hUsed : (Fintype.card L-1)*cap ≤ used)
    (hCoeff : 0 ≤ d-ε) (hSlack : 0 ≤ (d-ε)*(a:ℝ)-(used:ℝ))
    (hNeed : (b:ℝ) ≤ ((d-ε)*(a:ℝ)-(used:ℝ))*(a:ℝ)) :
    ∃ F : L → Finset (V × V),
      (∀ l, digraphOfArcs (F l) ≤ reserve) ∧
      (∀ l l', l ≠ l' → Disjoint (F l) (F l')) ∧
      (∀ l e, e ∈ F l → ∃ u v, e.1 ∈ eligible l u ∧ e.2 ∈ eligible l v ∧
        u ∈ Set.range (shadowSend (factor l) (incoming l) (outgoing l)) ∧
        v ∈ Set.range (shadowReceive (factor l) (incoming l) (outgoing l))) ∧
      (∀ l x, inDegree (digraphOfArcs (F l)) x ≤ Fintype.card U*cap ∧
        outDegree (digraphOfArcs (F l)) x ≤ Fintype.card U*cap) ∧
      ∀ l u, sout l u+clusterArcMass (label l) (F l) true u =
        sin l (factor l u)+clusterArcMass (label l) (F l) false (factor l u) := by
  let send l := shadowSend (factor l) (incoming l) (outgoing l)
  let receive l := shadowReceive (factor l) (incoming l) (outgoing l)
  let q l := shadowPairDemand (send l) (receive l) (M l)
  have hDemand (l : L) (u v : U) : q l u v ≤ if Q.Adj u v then b else 0 :=
    shadowPairDemand_le Q (send l) (receive l) (M l) b (hSupport l) u v
  have hBatch (u v : U) : ∃ C : L → Finset (V × V),
      (∀ l, C l ⊆ arcRectangle (pair u v) (eligible l u) (eligible l v) ∧ (C l).card = q l u v ∧
        (∀ x, ((C l).filter (fun e => e.1 = x)).card ≤ cap) ∧
        ∀ y, ((C l).filter (fun e => e.2 = y)).card ≤ cap) ∧
      ∀ l k, l ≠ k → Disjoint (C l) (C k) := by
    by_cases h : Q.Adj u v
    · have hq (l : L) : q l u v ≤ b := by simpa only [if_pos h] using hDemand l u v
      exact exists_balancing_batches (pair u v) (base u) (base v) (fun l => eligible l u) (fun l => eligible l v)
        ε d (fun l => q l u v) cap loss a a used (hRegular u v h).1 (hRegular u v h).2
        (fun l => hEligible l u) (fun l => hEligible l v) ha ha hcap
        (fun l => (hq l).trans hLoss) (fun l => hSize l u) (fun l => hSize l v)
        (hLarge u) (hLarge v) hUsed hCoeff hSlack
        (fun l => (show (q l u v:ℝ) ≤ b by exact_mod_cast hq l).trans hNeed)
    · have hZero (l : L) : q l u v = 0 :=
        Nat.eq_zero_of_le_zero (by simpa only [if_neg h] using hDemand l u v)
      exact ⟨fun _ => ∅,fun l => by simp [hZero l],by simp⟩
  choose C hC hCDis using hBatch
  have hArc {l : L} {u v : U} {e : V × V} (h : e ∈ C u v l) :
      e.1 ∈ eligible l u ∧ e.2 ∈ eligible l v ∧ (pair u v).Adj e.1 e.2 :=
    (mem_arcRectangle _ _ _ _).mp ((hC u v l).1 h)
  have hPairDis (u v u' v' : U) (l l' : L) (hne : (u,v) ≠ (u',v')) : Disjoint (C u v l) (C u' v' l') := by
    apply disjoint_left.mpr
    intro e h h'
    have hs : u = u' := Classical.byContradiction fun hh =>
      disjoint_left.mp (hBase u u' hh) (hEligible _ _ (hArc h).1) (hEligible _ _ (hArc h').1)
    have ht : v = v' := Classical.byContradiction fun hh =>
      disjoint_left.mp (hBase v v' hh) (hEligible _ _ (hArc h).2.1) (hEligible _ _ (hArc h').2.1)
    exact hne (Prod.ext hs ht)
  have hMatrixCards (l : L) (v w : ↥(incoming l ∪ outgoing l)) :
      (C (send l v) (receive l w) l).card = M l v w := by
    have hs : Function.Injective (send l) := shadowSend_injective _ _ _ (hSep l)
    have hr : Function.Injective (receive l) := (factor l).injective.comp hs
    exact ((hC _ _ l).2.1).trans (shadowPairDemand_at_endpoints _ _ _ hs hr _ _)
  obtain ⟨F,hF,hFDis,hBalance⟩ := balanced_layers_of_shared_batches factor incoming outgoing label sin sout c M C
    hDis hSep hIn hOut (fun l u v e h => ⟨hLabel l u _ (hArc h).1,hLabel l v _ (hArc h).2.1⟩)
    hCDis hPairDis hMatrixCards hRow hCol
  refine ⟨F,?_,hFDis,?_,?_,hBalance⟩
  · intro l x y h
    obtain ⟨u,v,h'⟩ := hF l (x,y) h
    exact hReserve u v (hArc h').2.2
  · intro l e h
    obtain ⟨u,v,h'⟩ := hF l e h
    have hPos : 0 < q l u v := ((hC u v l).2.1) ▸ card_pos.mpr ⟨e,h'⟩
    have hs : u ∈ Set.range (send l) := Classical.byContradiction fun he => by
      simpa only [q,shadowPairDemand,dif_neg he,lt_self_iff_false] using hPos
    have hr : v ∈ Set.range (receive l) := Classical.byContradiction fun he => by
      simpa only [q,shadowPairDemand,dif_pos hs,dif_neg he,lt_self_iff_false] using hPos
    exact ⟨u,v,(hArc h').1,(hArc h').2.1,hs,hr⟩
  · intro l x
    exact batch_union_degree_le base (fun u v => C u v l) (F l) cap hBase
      (fun u v e h => ⟨hEligible _ _ (hArc h).1,hEligible _ _ (hArc h).2.1⟩)
      (fun u v => (hC u v l).2.2) (hF l) x

end OverfullWork.DirectedRobustExpansion
