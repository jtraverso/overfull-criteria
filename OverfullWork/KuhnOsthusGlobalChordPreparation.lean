module

public import OverfullWork.KuhnOsthusChordRoundPreparation
public import OverfullWork.KuhnOsthusChordRoundGrouping
public import OverfullWork.KuhnOsthusRegularResiduePartition

@[expose] public section


/-! Preparation of all chord rounds in Kühn–Osthus Lemma 9.7. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedDemandHall
open scoped Classical
variable {V I S : Type*} [Fintype V] [Fintype I] [Fintype S]

set_option maxHeartbeats 600000 in
/-- Split the ordinary residue into permutation factors, assign the exceptional
path systems within each round, and use the entire walk bank. The resulting
systems partition the required physical arcs. -/
theorem prepare_chord_systems_from_interval_cells
    {r n b d g f t u scale ell k m : ℕ} [NeZero g] [NeZero (b*10)]
    (Z : Finset V) (rank : ↥Zᶜ → Fin (n+2)) (quarter : ↥Zᶜ → Fin 4)
    (parent : Fin (n+2) → I) (s : Equiv.Perm I) (root : I)
    (H : Digraph ↥Zᶜ) (coarse : ↥Zᶜ → Fin g)
    (A : Fin f → Finset ↥Zᶜ) (owner : Fin f → Fin g) (next : Equiv.Perm (Fin f))
    (cells : Fin f × S → Finset ↥Zᶜ) (slot : Fin (b*10) ≃ Fin f × (S × Fin t))
    (C : Fin r → Fin f × (S × Fin t) → Digraph V)
    (walkOwner : Fin (n+2) → I) (Q : Fin (n+2) × Fin 4 → Finset ↥Zᶜ)
    (M : ∀ j : Fin (n+2) × Fin 4, Fin (r*k) → Q j ≃ Q (finRotate (n+2) j.1,j.2))
    (hReg : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hLoop : ∀ v, ¬ H.Adj v v) (hd : 0 < d) (hSize : 3*d ≤ Fintype.card ↥Zᶜ)
    (hLarge : 802 ≤ g) (hCount : b*10 = d*3*g.choose 2) (hSlots : 200 ≤ b*10)
    (hCoarse : 200*g ≤ g.choose 2) (hFine : 400*u ≤ f) (ht : 300*t ≤ b*10)
    (hOwner : ∀ j v, v ∈ A j → coarse v = owner j)
    (hOwnerSize : ∀ a, (finiteSatisfying (fun j => owner j = a)).card ≤ u)
    (hCellSub : ∀ j, cells j ⊆ A j.1)
    (hApart : ∀ i j, i ≠ j → Disjoint (cells i) (cells j))
    (hCycle : ∀ i, s.SameCycle root i)
    (hPos : 0 < k*m) (hScale : 24 ≤ scale) (hRoom : 3*(130*scale) ≤ m)
    (hWalkSize : ∀ j, (Q j).card = m)
    (hWalkCell : ∀ j v, v ∈ Q j → rank v = j.1 ∧ quarter v = j.2)
    (hBank : ∀ j p q, p ≠ q → ∀ x, M j p x ≠ M j q x)
    (hLo : (b*10)*(12*scale) ≤ 4*(k*m)) (hHi : 4*(k*m) ≤ (b*10)*(12*(scale+1)))
    (hFibre : ∀ x, (finiteSatisfying (fun j => parent j = x)).card = ell)
    (hCluster : ∀ x, (finiteSatisfying (fun v => parent (rank v) = x)).card =
      (finiteSatisfying (fun v => parent (rank v) = s x)).card)
    (hBlock : ∀ j x,
      (∑ e, if walkOwner e = j ∧ parent e = x then (1:ℕ) else 0) + (if j = x then 1 else 0) =
      (∑ e, if walkOwner e = j ∧ parent (finRotate (n+2) e) = s x then (1:ℕ) else 0) +
        (if j = s x then 1 else 0))
    (hCap : 3*(2*g^2*Fintype.card ↥Zᶜ/(b*10)) ≤ scale)
    (hDisC : ∀ i j : Fin r × (Fin f × (S × Fin t)), i ≠ j →
      Disjoint (C i.1 i.2) (C j.1 j.2))
    (hC : ∀ a i, IsDirectedPathSystem (C a i) ∧ CoversExceptional (C a i) Z)
    (hNo : ∀ a i x y, (C a i).Adj x y → x ∈ Z → y ∉ Z) :
    letI : DecidableEq ↥Zᶜ := Classical.decEq _
    let basic a i := basicExceptionalPathSystem (C a i) Z
    let support a i := finiteSatisfying (IncidentTo (basic a i))
    let c := parent ∘ rank
    let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
    let rotate := (finRotate (n+2)).prodCongr (Equiv.refl (Fin 4))
    let U := successorCellMatchingUnion Q rotate M
    let E := ⨆ i : Fin r × (Fin f × (S × Fin t)), C i.1 i.2
    Disjoint H U → Disjoint (liftDirectedPair e e H ⊔ liftDirectedPair e e U) E →
    (∀ a i, support a i ⊆ cells (i.1,i.2.1) ∪ cells (next i.1,i.2.1)) →
    (∀ a i x, (finiteSatisfying (fun v => c v = x ∧ IncidentTo (basic a i) v)).card
      ≤ 2*g^2*Fintype.card ↥Zᶜ/(b*10)) →
    (∀ a i x, (∑ p : Arc (basic a i), if c p.val.1 = x then (1:ℕ) else 0) =
      ∑ p : Arc (basic a i), if c p.val.2 = s x then (1:ℕ) else 0) →
    Nonempty (PreparedChordSystems (liftDirectedPair e e H ⊔ liftDirectedPair e e U ⊔ E)
      Z c s (scale+2*(ell*(13*scale))) (Fin (r*(b*10)))) := by
  classical
  intro basic support c e rotate U E hHU hDis hSupport hTouch hBalance
  have hFactors := partition_regular_residue_with_permutations H r d hReg hLoop coarse
    hd hSize hLarge
  dsimp only at hFactors
  rw [←hCount] at hFactors
  obtain ⟨σ,F,P,hσ,hF,hFO,_⟩ := hFactors
  let banks (a : Fin r) (j : Fin (n+2) × Fin 4) (p : Fin k) :=
    M j (finProdFinEquiv (a,p))
  let U' (a : Fin r) := successorCellMatchingUnion Q rotate (banks a)
  let E' (a : Fin r) := ⨆ i, C a i
  have hQApart (i j : Fin (n+2) × Fin 4) (hne : i ≠ j) : Disjoint (Q i) (Q j) := by
    rw [disjoint_left]
    intro v hi hj
    obtain ⟨hi₁,hi₂⟩ := hWalkCell i v hi
    obtain ⟨hj₁,hj₂⟩ := hWalkCell j v hj
    exact hne (Prod.ext (hi₁.symm.trans hj₁) (hi₂.symm.trans hj₂))
  have hBanks := partition_successor_matching_bank Q rotate M hQApart hBank
  obtain ⟨hUO,hU,_⟩ := hBanks
  have hE (a : Fin r) : E' a ≤ E :=
    iSup_le (fun i => le_iSup (fun q : Fin r × (Fin f × (S × Fin t)) => C q.1 q.2) (a,i))
  have hEO (x y : V) (hxy : E.Adj x y) : ∃! a, (E' a).Adj x y := by
    obtain ⟨⟨a,i⟩,hi⟩ := Digraph.iSup_adj.mp hxy
    refine ⟨a,Digraph.iSup_adj.mpr ⟨i,hi⟩,?_⟩
    intro a' ha'
    obtain ⟨i',hi'⟩ := Digraph.iSup_adj.mp ha'
    by_contra hne
    exact disjoint_iff_inf_le.mp (hDisC (a',i') (a,i) (fun he => hne (congrArg Prod.fst he)))
      ⟨hi',hi⟩
  let W (a : Fin r) := liftDirectedPair e e (U' a ⊔ F a) ⊔ E' a
  have hRounds (a : Fin r) : Nonempty
      (PreparedChordSystems (W a) Z c s (scale+2*(ell*(13*scale))) (Fin (b*10))) := by
    obtain ⟨assign,hLocal,hSeparated⟩ := assign_exceptional_systems_to_ordered_residue
      (P a) next A owner cells (support a) slot u hSlots hCount hCoarse hFine ht
      hOwner hOwnerSize hCellSub hApart (hSupport a)
    let D (i : Fin (b*10)) := C a (assign i)
    have hDO (x y : V) (hxy : (E' a).Adj x y) : ∃! i, (D i).Adj x y := by
      obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp hxy
      refine ⟨assign.symm j,by simpa only [D,Equiv.apply_symm_apply] using hj,?_⟩
      intro i hi
      apply assign.injective
      rw [Equiv.apply_symm_apply]
      by_contra hn
      exact disjoint_iff_inf_le.mp
        (hDisC (a,assign i) (a,j) (fun he => hn (congrArg Prod.snd he))) ⟨hi,hj⟩
    have hRoundDis : Disjoint (liftDirectedPair e e (U' a ⊔ F a)) (E' a) := by
      apply hDis.mono ?_ (hE a)
      rw [lift_directed_pair_sup, sup_comm]
      exact sup_le_sup (liftDirectedPair_mono e e (hF a)) (liftDirectedPair_mono e e (hU a))
    apply prepare_original_chord_round Z rank quarter parent s root (σ a) (F a) coarse
      (P a) (E' a) D walkOwner Q (banks a) hCycle (hσ a) hPos (by omega) hScale hRoom
      hWalkSize hWalkCell
      (fun j p q hp x => hBank j _ _ (fun he => hp (congrArg Prod.snd (finProdFinEquiv.injective he))) x)
      hLo hHi hFibre hCluster hBlock hCap
      (fun i => le_iSup (C a) (assign i)) hDO (fun i => hC a (assign i))
      (fun i => hNo a (assign i))
      (hHU.symm.mono (hU a) (hF a)) hRoundDis hLocal
      ?_ (fun i => hTouch a (assign i)) (fun i => hBalance a (assign i))
    intro i j hij
    letI : DecidableEq ↥Zᶜ := Classical.decEq _
    have hFootprint (G₁ G₂ : Digraph ↥Zᶜ) :
        finiteSatisfying (IncidentTo (G₁ ⊔ G₂)) =
          finiteSatisfying (IncidentTo G₁) ∪ finiteSatisfying (IncidentTo G₂) := by
      simpa only [true_and] using chord_footprint_sup G₁ G₂ (fun _ => True)
    simpa only [hFootprint] using hSeparated i j hij
  obtain ⟨hW,hWO⟩ := combine_chord_round_arc_owners Z H U E F U' E' hHU
    hF hU hE (fun x y => (hFO x y).mp) (fun x y => (hUO x y).mp) hEO hDis
  exact ⟨(combine_prepared_chord_rounds _ W Z c s _ (fun a => Classical.choice (hRounds a))
    hW hWO).reindex finProdFinEquiv.symm⟩

end OverfullWork.DirectedRobustExpansion
