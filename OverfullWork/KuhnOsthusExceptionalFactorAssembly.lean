module

public import OverfullWork.KuhnOsthusOriginalInterval
public import OverfullWork.KuhnOsthusExceptionalFactorPacking

@[expose] public section


/-! Assemble the original exceptional paths of Kühn–Osthus Lemma 7.6.
Neighbouring intervals share a boundary. The ending interval owns
the incoming slot and the starting interval owns the outgoing slot. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedSpanningConfiguration
open scoped Classical
variable {V : Type*} [Fintype V]

/-- The physical union, including every copy of the exceptional
incidences carried by the distinct interval–style pairs. -/
def OriginalExceptionalFactor.digraph {label : V → Fin 50} {Z : Finset V} {l : ℕ}
    (C : OriginalExceptionalFactor label Z l) : Digraph V := ⨆ i, C.path i

private theorem slot_card {A : Type*} (S : Finset A)
    (hUnique : ∀ a ∈ S, ∀ b ∈ S, a = b) :
    S.card = if S.Nonempty then 1 else 0 := by
  classical
  by_cases h : S.Nonempty
  · obtain ⟨a,ha⟩ := h
    rw [if_pos ⟨a,ha⟩,card_eq_one]
    exact ⟨a,eq_singleton_iff_unique_mem.mpr ⟨ha,fun b hb => hUnique b hb a ha⟩⟩
  · rw [if_neg h,card_eq_zero]
    exact not_nonempty_iff_eq_empty.mp h

/-- In a path system, occupied incoming and outgoing slots have degree one. -/
theorem path_system_degree_slots (G : Digraph V) (hG : IsDirectedPathSystem G) (v : V) :
    (outDegree G v = if ∃ w, G.Adj v w then 1 else 0) ∧
    (inDegree G v = if ∃ w, G.Adj w v then 1 else 0) := by
  classical
  constructor
  · unfold outDegree
    have h := slot_card (univ.filter (G.Adj v)) (fun a ha b hb =>
      hG.out_unique (mem_filter.mp ha).2 (mem_filter.mp hb).2)
    simpa only [Finset.Nonempty,mem_filter,mem_univ,true_and] using h
  · unfold inDegree inNeighbours
    have h := slot_card (univ.filter (fun a => G.Adj a v)) (fun a ha b hb =>
      hG.in_unique (mem_filter.mp ha).2 (mem_filter.mp hb).2)
    simpa only [Finset.Nonempty,mem_filter,mem_univ,true_and] using h

/-- Each ordinary vertex has exactly one incoming and one outgoing
interval slot. Each exceptional vertex has one of each per interval. -/
theorem original_interval_factor_exact_semidegrees {J : Type*} [Fintype J]
    {G : Digraph V} {Z : Finset V} {A S T : J → Finset V}
    (P : ∀ i, OriginalInterval G Z (A i) (S i) (T i))
    (hOut : ∀ x ∉ Z, ∃! i, x ∈ A i \ T i)
    (hIn : ∀ x ∉ Z, ∃! i, x ∈ A i \ S i) :
    let D := ⨆ i, (P i).digraph
    Pairwise (fun i j => Disjoint (P i).digraph (P j).digraph) ∧
      ∀ x, let d := if x ∈ Z then Fintype.card J else 1
        inDegree D x = d ∧ outDegree D x = d := by
  intro D
  have hDis : Pairwise (fun i j => Disjoint (P i).digraph (P j).digraph) := by
    intro i j hij
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hi,hj⟩
    by_cases hx : x ∈ Z
    · have hy := (P i).no_internal hi hx
      obtain ⟨k,_,hUnique⟩ := hIn y hy
      exact hij ((hUnique i (((P i).slots y hy).2.mp ⟨x,hi⟩)).trans
        (hUnique j (((P j).slots y hy).2.mp ⟨x,hj⟩)).symm)
    · obtain ⟨k,_,hUnique⟩ := hOut x hx
      exact hij ((hUnique i (((P i).slots x hx).1.mp ⟨y,hi⟩)).trans
        (hUnique j (((P j).slots x hx).1.mp ⟨y,hj⟩)).symm)
  refine ⟨hDis,?_⟩
  intro x d
  change inDegree (⨆ i, (P i).digraph) x = d ∧ outDegree (⨆ i, (P i).digraph) x = d
  rw [inDegree_iSup_of_disjoint _ hDis,outDegree_iSup_of_disjoint _ hDis]
  by_cases hx : x ∈ Z
  · have hO (i : J) : outDegree (P i).digraph x = 1 := by
      rw [(path_system_degree_slots _ (P i).path_system x).1,if_pos ((P i).cover x hx).1]
    have hI (i : J) : inDegree (P i).digraph x = 1 := by
      rw [(path_system_degree_slots _ (P i).path_system x).2,if_pos ((P i).cover x hx).2]
    simp [d,hx,hO,hI]
  · obtain ⟨i,hi,hUi⟩ := hOut x hx
    obtain ⟨j,hj,hUj⟩ := hIn x hx
    dsimp only [d]
    rw [if_neg hx]
    constructor
    · rw [sum_eq_single j]
      · rw [(path_system_degree_slots _ (P j).path_system x).2,
          if_pos (((P j).slots x hx).2.mpr hj)]
      · intro k _ hk
        rw [(path_system_degree_slots _ (P k).path_system x).2,
          if_neg (fun he => hk (hUj k (((P k).slots x hx).2.mp he)))]
      · simp
    · rw [sum_eq_single i]
      · rw [(path_system_degree_slots _ (P i).path_system x).1,
          if_pos (((P i).slots x hx).1.mpr hi)]
      · intro k _ hk
        rw [(path_system_degree_slots _ (P k).path_system x).1,
          if_neg (fun he => hk (hUi k (((P k).slots x hx).1.mp he)))]
      · simp

/-- Assemble the exact certificate required by Lemma 8.1. The slot
conditions allow boundary vertices to occur in two of the intervals. -/
theorem assemble_original_exceptional_factor (G : Digraph V)
    (Z : Finset V) (label : V → Fin 50) (l : ℕ)
    (A S T : Fin 50 × Fin l → Finset V)
    (P : ∀ i, OriginalInterval G Z (A i) (S i) (T i))
    (hStyle : ∀ i x, x ∈ A i → label x = i.1)
    (hSize : ∀ i, (((A i \ T i).card):ℝ) ≤ (Fintype.card V:ℝ)/(50*l))
    (hOut : ∀ x ∉ Z, ∃! i, x ∈ A i \ T i)
    (hIn : ∀ x ∉ Z, ∃! i, x ∈ A i \ S i) :
    ∃ C : OriginalExceptionalFactor label Z l, (∀ i, C.path i = (P i).digraph) ∧
      C.digraph ≤ G ∧
      ∀ x, inDegree C.digraph x = (if x ∈ Z then 50*l else 1) ∧
        outDegree C.digraph x = (if x ∈ Z then 50*l else 1) := by
  classical
  have hOwnerOut {i j : Fin 50 × Fin l} {x : V} (hx : x ∉ Z)
      (hi : ∃ y, (P i).digraph.Adj x y) (hj : ∃ y, (P j).digraph.Adj x y) : i = j := by
    obtain ⟨k,_,hk⟩ := hOut x hx
    exact (hk i (((P i).slots x hx).1.mp hi)).trans (hk j (((P j).slots x hx).1.mp hj)).symm
  have hOwnerIn {i j : Fin 50 × Fin l} {x : V} (hx : x ∉ Z)
      (hi : ∃ y, (P i).digraph.Adj y x) (hj : ∃ y, (P j).digraph.Adj y x) : i = j := by
    obtain ⟨k,_,hk⟩ := hIn x hx
    exact (hk i (((P i).slots x hx).2.mp hi)).trans (hk j (((P j).slots x hx).2.mp hj)).symm
  have hOwnerInterior {i j : Fin 50 × Fin l} {x : V} (hx : x ∉ Z)
      (hi : IncidentTo (exceptionalPart (P i).digraph Z) x)
      (hj : IncidentTo (exceptionalPart (P j).digraph Z) x) : i = j := by
    have hOwn (k : Fin 50 × Fin l) (h : IncidentTo (exceptionalPart (P k).digraph Z) x) :
        ∃ y, (P k).digraph.Adj x y := by
      have hp := mem_sdiff.mp ((P k).exceptional_inside x hx h)
      exact ((P k).slots x hx).1.mpr (mem_sdiff.mpr ⟨hp.1,fun ht => hp.2 (mem_union_right _ ht)⟩)
    exact hOwnerOut hx (hOwn i hi) (hOwn j hj)
  let C : OriginalExceptionalFactor label Z l := {
    path := fun i => (P i).digraph
    path_system := fun i => (P i).path_system
    cover := fun i => (P i).cover
    no_internal := fun i => (P i).no_internal
    style := by
      intro i x hx h
      apply mem_singleton.mpr
      apply hStyle i x
      rcases h with ⟨y,hy⟩ | ⟨y,hy⟩
      · exact (mem_sdiff.mp (((P i).slots x hx).1.mp ⟨y,hy⟩)).1
      · exact (mem_sdiff.mp (((P i).slots x hx).2.mp ⟨y,hy⟩)).1
    size := by
      intro i
      have hNat := original_exceptional_path_size_from_sources
        (D := (P i).digraph) (S := A i \ T i) (Z := Z) (P i).path_system (by
          intro x y h
          by_cases hx : x ∈ Z
          · exact mem_union_right _ hx
          · exact mem_union_left _ (((P i).slots x hx).1.mp ⟨y,h⟩))
      have hCount : (Fintype.card (DirectedDemandHall.Arc (P i).digraph):ℝ) ≤
          (((A i \ T i).card):ℝ) + Z.card := by exact_mod_cast hNat
      exact hCount.trans (add_le_add (hSize i) le_rfl)
    disjoint := by
      intro i j x y hi hj
      by_cases hx : x ∈ Z
      · exact hOwnerIn ((P i).no_internal hi hx) ⟨x,hi⟩ ⟨x,hj⟩
      · exact hOwnerOut hx ⟨y,hi⟩ ⟨y,hj⟩
    ordinary_out := by
      intro i j x y z hx hy hz
      have h := hOwnerOut hx ⟨y,hy.1⟩ ⟨z,hz.1⟩
      subst j
      exact (P i).path_system.out_unique hy.1 hz.1
    ordinary_in := by
      intro i j x y z hx hy hz
      have h := hOwnerIn hx ⟨y,hy.1⟩ ⟨z,hz.1⟩
      subst j
      exact (P i).path_system.in_unique hy.1 hz.1
    ordinary_match := by
      intro i j x y z hx hy hz
      have h := hOwnerInterior hx (Or.inr ⟨y,hy⟩) (Or.inl ⟨z,hz⟩)
      subst j
      exact (P i).exceptional_matching hx hy hz }
  refine ⟨C,fun _ => rfl,iSup_le (fun i => (P i).le),?_⟩
  intro x
  simpa only [OriginalExceptionalFactor.digraph,C,Fintype.card_prod,Fintype.card_fin] using
    (original_interval_factor_exact_semidegrees P hOut hIn).2 x

omit [Fintype V] in
/-- The ordinary interval partition comes from including the starting
cell of each interval and omitting its terminal cell. Restore that
terminal cell from the next interval, and compute the two slot owners. -/
theorem exceptional_interval_slot_owners {I : Type*} (next : Equiv.Perm I)
    (U S : I → Finset V) (hNext : ∀ i, next i ≠ i)
    (hSub : ∀ i, S i ⊆ U i)
    (hDis : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    (∀ i, ((U i ∪ S (next i)) \ S (next i)) = U i) ∧
    ∀ x, (∃ i, x ∈ U i) → ∃! i, x ∈ (U i ∪ S (next i)) \ S i := by
  have hUnique {x : V} {i j : I} (hi : x ∈ U i) (hj : x ∈ U j) : i = j :=
    by_contra fun h => disjoint_left.mp (hDis i j h) hi hj
  have hApart {x : V} {i : I} (hi : x ∈ U i) : x ∉ S (next i) := fun h =>
    hNext i (hUnique (hSub _ h) hi)
  refine ⟨?_,?_⟩
  · intro i
    ext x
    simp only [mem_sdiff,mem_union]
    exact ⟨fun ⟨h,hn⟩ => h.resolve_right hn,fun h => ⟨Or.inl h,hApart h⟩⟩
  · rintro x ⟨j,hj⟩
    by_cases hS : x ∈ S j
    · have hPrev : next.symm j ≠ j := by
        intro h
        exact hNext (next.symm j) ((next.apply_symm_apply j).trans h.symm)
      have hNot : x ∉ S (next.symm j) := fun h =>
        hPrev (hUnique (hSub _ h) hj)
      refine ⟨next.symm j,mem_sdiff.mpr ⟨mem_union_right _ (by rwa [next.apply_symm_apply]),hNot⟩,?_⟩
      intro i hi
      obtain ⟨hi,hN⟩ := mem_sdiff.mp hi
      rcases mem_union.mp hi with hi | hi
      · exact (hN ((hUnique hi hj).symm ▸ hS)).elim
      · apply next.injective
        rw [next.apply_symm_apply]
        exact hUnique (hSub _ hi) hj
    · refine ⟨j,mem_sdiff.mpr ⟨mem_union_left _ hj,hS⟩,?_⟩
      intro i hi
      rcases mem_union.mp (mem_sdiff.mp hi).1 with hi | hi
      · exact hUnique hi hj
      · exact (hS (hUnique (hSub _ hi) hj ▸ hi)).elim

/-- Assemble a factor over the cyclic intervals, each with its style.
Each interval owns a common number of ordinary vertices. -/
theorem assemble_exceptional_factor_along_intervals (G : Digraph V)
    (Z : Finset V) (label : V → Fin 50) (l m : ℕ)
    (next : Equiv.Perm (Fin 50 × Fin l)) (U S : Fin 50 × Fin l → Finset V)
    (hNext : ∀ i, next i ≠ i) (hNextStyle : ∀ i, (next i).1 = i.1)
    (hSub : ∀ i, S i ⊆ U i)
    (hDis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ U i)
    (hSize : ∀ i, (U i).card = m) (hStyle : ∀ i x, x ∈ U i → label x = i.1)
    (P : ∀ i, OriginalInterval G Z (U i ∪ S (next i)) (S i) (S (next i))) :
    ∃ C : OriginalExceptionalFactor label Z l, (∀ i, C.path i = (P i).digraph) ∧
      C.digraph ≤ G ∧
      ∀ x, inDegree C.digraph x = (if x ∈ Z then 50*l else 1) ∧
        outDegree C.digraph x = (if x ∈ Z then 50*l else 1) := by
  classical
  obtain ⟨hSlots,hIn⟩ := exceptional_interval_slot_owners next U S hNext hSub hDis
  apply assemble_original_exceptional_factor G Z label l (fun i => U i ∪ S (next i))
    S (fun i => S (next i)) P
  · intro i x hx
    rcases mem_union.mp hx with hu | ht
    · exact hStyle i x hu
    · exact (hStyle _ x (hSub _ ht)).trans (hNextStyle i)
  · intro i
    have hCount : ((univ : Finset (Fin 50 × Fin l)).biUnion U).card = (50*l)*m := by
      rw [card_biUnion (fun i _ j _ h => hDis i j h)]
      simp [hSize]
    have hTotal : (50*l)*m ≤ Fintype.card V :=
      hCount.symm ▸ card_le_univ (univ.biUnion U)
    have hp : (0:ℝ) < 50*(l:ℝ) := by
      have hl : 0 < l := Nat.zero_lt_of_lt i.2.isLt
      exact mul_pos (by norm_num) (by exact_mod_cast hl)
    rw [hSlots i,hSize i]
    apply (le_div_iff₀ hp).mpr
    rw [mul_comm]
    exact_mod_cast hTotal
  · intro x hx
    obtain ⟨i,hi⟩ := hCover x hx
    refine ⟨i,?_,?_⟩
    · change x ∈ (U i ∪ S (next i)) \ S (next i)
      rwa [hSlots i]
    intro j hj
    change x ∈ (U j ∪ S (next j)) \ S (next j) at hj
    rw [hSlots j] at hj
    exact by_contra fun h => disjoint_left.mp (hDis j i h) hj hi
  · exact fun x hx => hIn x (hCover x hx)

/-- Apply the deletion induction to actual interval covers. The
resulting original factors can be passed straight to Lemma 8.1. -/
theorem pack_exceptional_factors_of_residual_intervals (G : Digraph V)
    (Z : Finset V) (label : V → Fin 50) (r l m : ℕ)
    (next : Equiv.Perm (Fin 50 × Fin l)) (U S : Fin 50 × Fin l → Finset V)
    (hNext : ∀ i, next i ≠ i) (hNextStyle : ∀ i, (next i).1 = i.1)
    (hSub : ∀ i, S i ⊆ U i)
    (hDis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ U i)
    (hSize : ∀ i, (U i).card = m) (hStyle : ∀ i x, x ∈ U i → label x = i.1)
    (hLocal : ∀ t < r, ∀ H : Digraph V, H ≤ G →
      (∀ v, inDegree H v ≤ t*(if v ∈ Z then 50*l else 1) ∧
        outDegree H v ≤ t*(if v ∈ Z then 50*l else 1)) →
      ∀ i, Nonempty (OriginalInterval (G \ H) Z (U i ∪ S (next i)) (S i) (S (next i)))) :
    ∃ C : Fin r → OriginalExceptionalFactor label Z l,
      (∀ i, (C i).digraph ≤ G) ∧ Pairwise (fun i j => Disjoint (C i).digraph (C j).digraph) ∧
      ∀ v, inDegree (⨆ i, (C i).digraph) v ≤ r*(if v ∈ Z then 50*l else 1) ∧
        outDegree (⨆ i, (C i).digraph) v ≤ r*(if v ∈ Z then 50*l else 1) := by
  let Cert (D : Digraph V) := ∃ C : OriginalExceptionalFactor label Z l, C.digraph = D
  have hPick (t : ℕ) (ht : t < r) (H : Digraph V) (hH : H ≤ G)
      (hBudget : ∀ v, inDegree H v ≤ t*(if v ∈ Z then 50*l else 1) ∧
        outDegree H v ≤ t*(if v ∈ Z then 50*l else 1)) :
      ∃ D : Digraph V, D ≤ G \ H ∧ Cert D ∧
        ∀ v, inDegree D v ≤ (if v ∈ Z then 50*l else 1) ∧
          outDegree D v ≤ (if v ∈ Z then 50*l else 1) := by
    classical
    let P i := Classical.choice (hLocal t ht H hH hBudget i)
    obtain ⟨C,_,hLe,hDegree⟩ := assemble_exceptional_factor_along_intervals (G \ H) Z
      label l m next U S hNext hNextStyle hSub hDis hCover hSize hStyle P
    exact ⟨C.digraph,hLe,⟨C,rfl⟩,fun v => ⟨(hDegree v).1.le,(hDegree v).2.le⟩⟩
  obtain ⟨F,hF,hApart,hLoss⟩ := exists_disjoint_exceptional_factor_packing G Z r 50 l Cert hPick
  choose C hC using fun i => (hF i).2
  refine ⟨C,fun i => (hC i).symm ▸ (hF i).1,?_,?_⟩
  · intro i j hij
    rw [hC,hC]
    exact hApart hij
  · simpa only [hC] using hLoss

end OverfullWork.DirectedRobustExpansion
