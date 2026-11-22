module

public import OverfullWork.OsthusStadenBalancingBatches
public import OverfullWork.OsthusStadenShadowFibres

@[expose] public section


/-! Project the actual H2 arcs back to their cluster pairs, and
transfer the shadow degree equations to the physical red counts. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

noncomputable def clusterArcMass {U V : Type*} (label : V → Option U)
    (S : Finset (V × V)) (outgoing : Bool) (u : U) : ℕ :=
  (S.filter fun e => label (if outgoing then e.1 else e.2) = some u).card

theorem clusterArcMass_of_pair_selection {T U V : Type*} [Fintype T]
    (label : V → Option U) (send receive : T → U)
    (C : T → T → Finset (V × V))
    (hSend : Function.Injective send) (hReceive : Function.Injective receive)
    (hEnd : ∀ i j e, e ∈ C i j → label e.1 = some (send i) ∧ label e.2 = some (receive j))
    (s : Bool) (u : U) :
    clusterArcMass label (univ.biUnion (fun ij : T × T => C ij.1 ij.2)) s u =
      ∑ ij : T × T, if (if s then send ij.1 else receive ij.2) = u then
        (C ij.1 ij.2).card else 0 := by
  have hDis (i j : T × T) (hij : i ≠ j) : Disjoint (C i.1 i.2) (C j.1 j.2) := by
    rw [disjoint_left]
    intro e hi hj
    have h₁ := hSend (Option.some.inj ((hEnd _ _ _ hi).1.symm.trans (hEnd _ _ _ hj).1))
    have h₂ := hReceive (Option.some.inj ((hEnd _ _ _ hi).2.symm.trans (hEnd _ _ _ hj).2))
    exact hij (Prod.ext h₁ h₂)
  unfold clusterArcMass
  rw [filter_biUnion,card_biUnion (fun i _ j _ hij =>
    (hDis i j hij).mono (filter_subset _ _) (filter_subset _ _))]
  apply sum_congr rfl
  intro ij _
  have he (e : V × V) (h : e ∈ C ij.1 ij.2) :
      label (if s then e.1 else e.2) = some (if s then send ij.1 else receive ij.2) := by
    cases s
    · exact (hEnd _ _ _ h).2
    · exact (hEnd _ _ _ h).1
  by_cases hu : (if s then send ij.1 else receive ij.2) = u
  · rw [if_pos hu,filter_true_of_mem]
    intro e he'
    exact (he e he').trans (congrArg some hu)
  · rw [if_neg hu]
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro e hm h
    exact hu (Option.some.inj ((he e hm).symm.trans h))

/-- If the chosen H2 arc sets have the shadow multiplicities, their
union balances the physical successor pairs in every cluster. -/
theorem physical_successor_balance {U V : Type*}
    (σ : Equiv.Perm U) (incoming outgoing : Finset U)
    (label : V → Option U) (sin sout : U → ℕ) (c : ℕ)
    (C : ↥(incoming ∪ outgoing) → ↥(incoming ∪ outgoing) → Finset (V × V))
    (hDis : Disjoint incoming outgoing) (hSep : ∀ u ∈ outgoing, σ u ∉ incoming)
    (hIn : ∀ u, u ∉ incoming → sin u = 0) (hOut : ∀ u, u ∉ outgoing → sout u = 0)
    (hEnd : ∀ i j e, e ∈ C i j →
      label e.1 = some (shadowSend σ incoming outgoing i) ∧
      label e.2 = some (shadowReceive σ incoming outgoing j))
    (hRow : ∀ i, (∑ j,(C i j).card) = c+sin i)
    (hCol : ∀ j, (∑ i,(C i j).card) = c+sout j) :
    let S := univ.biUnion (fun ij : ↥(incoming ∪ outgoing) × ↥(incoming ∪ outgoing) => C ij.1 ij.2)
    ∀ u, sout u+clusterArcMass label S true u = sin (σ u)+clusterArcMass label S false (σ u) := by
  let T := ↥(incoming ∪ outgoing)
  let a : T → U := shadowSend σ incoming outgoing
  let b : T → U := shadowReceive σ incoming outgoing
  let S := (univ : Finset (T × T)).biUnion (fun ij => C ij.1 ij.2)
  have ha : Function.Injective a := shadowSend_injective σ incoming outgoing hSep
  have hb : Function.Injective b := σ.injective.comp ha
  have hMassOut (u : U) : clusterArcMass label S true u = ∑ i : T, (if a i = u then c+sin i else 0) := by
    rw [clusterArcMass_of_pair_selection label a b C ha hb hEnd,Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    by_cases h : a i = u
    · simpa only [if_true,h] using hRow i
    · simp [h]
  have hMassIn (u : U) : clusterArcMass label S false u = ∑ j : T, (if b j = u then c+sout j else 0) := by
    rw [clusterArcMass_of_pair_selection label a b C ha hb hEnd,Fintype.sum_prod_type,sum_comm]
    apply sum_congr rfl
    intro j _
    by_cases h : b j = u
    · simpa only [if_true,if_false,Bool.false_eq_true,h] using hCol j
    · simp [h]
  apply balance_after_shadow_demands σ incoming outgoing sin sout _ _ c hDis hSep hIn hOut
  · intro i
    rw [hMassOut,sum_eq_single i]
    · simp [a]
    · intro j _ h
      exact if_neg (fun he => h (ha he))
    · simp
  · intro i
    rw [hMassIn,sum_eq_single i]
    · simp [b]
    · intro j _ h
      exact if_neg (fun he => h (hb he))
    · simp
  · intro u hu
    rw [hMassOut]
    apply sum_eq_zero
    intro i _
    exact if_neg (fun h => hu ⟨i,h⟩)
  · intro u hu
    rw [hMassIn]
    apply sum_eq_zero
    intro i _
    exact if_neg (fun h => hu ⟨i,h⟩)

/-- Reserve pieces come in batches indexed by base pair and layer.
Selecting the two shifted endpoints preserves their multiplicities and
disjointness, and balances all layers simultaneously. -/
theorem balanced_layers_of_shared_batches {I U V : Type*} [Fintype I]
    (σ : I → Equiv.Perm U) (incoming outgoing : I → Finset U)
    (label : I → V → Option U) (sin sout : I → U → ℕ) (c : ℕ)
    (M : ∀ l : I, ↥(incoming l ∪ outgoing l) → ↥(incoming l ∪ outgoing l) → ℕ)
    (C : U → U → I → Finset (V × V))
    (hDis : ∀ l, Disjoint (incoming l) (outgoing l))
    (hSep : ∀ l u, u ∈ outgoing l → σ l u ∉ incoming l)
    (hIn : ∀ l u, u ∉ incoming l → sin l u = 0)
    (hOut : ∀ l u, u ∉ outgoing l → sout l u = 0)
    (hEnd : ∀ l u v e, e ∈ C u v l → label l e.1 = some u ∧ label l e.2 = some v)
    (hDistinctBatch : ∀ u v l l', l ≠ l' → Disjoint (C u v l) (C u v l'))
    (hDistinctPair : ∀ u v u' v' l l', (u,v) ≠ (u',v') → Disjoint (C u v l) (C u' v' l'))
    (hCard : ∀ l a b,
      (C (shadowSend (σ l) (incoming l) (outgoing l) a)
        (shadowReceive (σ l) (incoming l) (outgoing l) b) l).card = M l a b)
    (hRow : ∀ l a, (∑ b,M l a b) = c+sin l a)
    (hCol : ∀ l b, (∑ a,M l a b) = c+sout l b) :
    ∃ B : I → Finset (V × V),
      (∀ l, ∀ e ∈ B l, ∃ u v, e ∈ C u v l) ∧
      (∀ l l', l ≠ l' → Disjoint (B l) (B l')) ∧
      ∀ l u, sout l u+clusterArcMass (label l) (B l) true u =
        sin l (σ l u)+clusterArcMass (label l) (B l) false (σ l u) := by
  let T (l : I) := ↥(incoming l ∪ outgoing l)
  let a (l : I) : T l → U := shadowSend (σ l) (incoming l) (outgoing l)
  let b (l : I) : T l → U := shadowReceive (σ l) (incoming l) (outgoing l)
  let P (l : I) (u v : T l) := C (a l u) (b l v) l
  let B (l : I) := (univ : Finset (T l × T l)).biUnion (fun uv => P l uv.1 uv.2)
  refine ⟨B,?_,?_,?_⟩
  · intro l e he
    obtain ⟨⟨u,v⟩,_,he'⟩ := mem_biUnion.mp he
    exact ⟨a l u,b l v,he'⟩
  · intro l l' hne
    rw [disjoint_left]
    intro e he he'
    obtain ⟨⟨u,v⟩,_,h₁⟩ := mem_biUnion.mp he
    obtain ⟨⟨u',v'⟩,_,h₂⟩ := mem_biUnion.mp he'
    by_cases h : (a l u,b l v) = (a l' u',b l' v')
    · have hF : a l u = a l' u' := congrArg Prod.fst h
      have hS : b l v = b l' v' := congrArg Prod.snd h
      exact disjoint_left.mp (hDistinctBatch (a l u) (b l v) l l' hne) h₁
        (show e ∈ C (a l u) (b l v) l' by rw [hF,hS]; exact h₂)
    · exact disjoint_left.mp (hDistinctPair _ _ _ _ l l' h) h₁ h₂
  · intro l
    apply physical_successor_balance (σ l) (incoming l) (outgoing l) (label l) (sin l) (sout l) c
      (P l) (hDis l) (hSep l) (hIn l) (hOut l) (fun i j e h => hEnd l _ _ e h)
    · intro i
      change (∑ j,(C (a l i) (b l j) l).card) = _
      simp only [a,b,hCard]
      exact hRow l i
    · intro j
      change (∑ i,(C (a l i) (b l j) l).card) = _
      simp only [a,b,hCard]
      exact hCol l j

end OverfullWork.DirectedRobustExpansion
