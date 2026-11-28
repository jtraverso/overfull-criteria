module

public import OverfullWork.ChenShanGlobalAugmentation
public import OverfullWork.ChenShanSpecialFactorMargins
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset DirectedRobustExpansion
open scoped Classical

variable {V : Type*}

/-- A family of special factors, retaining the concrete reserve edges
that produced the occupied sets and those used to fill the paths. -/
structure SpecialFactorReserveRealization [Fintype V] [DecidableEq V] {B J E : Type*}
    [Fintype E] (A : B → ℕ → Finset V) (core : Finset V)
    (aug : V → V → Prop) (G : Digraph V)
    (blocked : B → J → Fin 2 → Finset V)
    (matching : E → B × J × Fin 2) (requests : B → J → Fin 2 → Finset E)
    (t n b cap : ℕ) where
  gL : E → V
  gR : E → V
  aug_edges : ∀ e, aug (gL e) (gR e) ∧ gL e ∉ blocked (matching e).1 (matching e).2.1 (matching e).2.2 ∧
    gR e ∉ blocked (matching e).1 (matching e).2.1 (matching e).2.2
  aug_fresh : Function.Injective (fun e => s(gL e,gR e))
  aug_cap : ∀ v, augmentationLoad univ gL gR v ≤ cap
  U : B → J → ℕ → Finset V
  W : B → J → ℕ → Finset V
  source_occupied : ∀ c j i, U c j i = A c i ∩
    (if i % 2 = 0 then blocked c j 0 ∪ (requests c j 0).image gL
      else blocked c j 1 ∪ (requests c j 1).image gR)
  target_occupied : ∀ c j i, W c j i = A c (i+1) ∩
    (if i % 2 = 0 then blocked c j 0 ∪ (requests c j 0).image gR
      else blocked c j 1 ∪ (requests c j 1).image gL)
  counts : ∀ c j i, i < t → (U c j i).card = b ∧ (W c j i).card = b
  paths : ∀ c j, OrderedClusterPaths
    ⟨fun x y => G.Adj x y ∨ ∃ i < t, x ∈ U c j i ∧ y ∈ W c j i⟩ (A c) (Fin n) 0 t
  preserves_occupied : ∀ c j i, i < t → ∀ k, (paths c j).vertex i k ∈ U c j i ↔
    (paths c j).vertex (i+1) k ∈ W c j i
  regular : ∀ j v, v ∈ core → (∃! w, (specialFactorDigraph (fun c => paths c j)).Adj v w) ∧
    (∃! w, (specialFactorDigraph (fun c => paths c j)).Adj w v)
  fill_in_reserve : ∀ c j (i : Fin t), specialPathFillingArcs (paths c j) (U c j i.val) i.val ≤ G
  fill_fresh : ∀ (p q : (B × Fin t) × J) x y u v,
    (specialPathFillingArcs (paths p.1.1 p.2) (U p.1.1 p.2 p.1.2.val) p.1.2.val).Adj x y →
    (specialPathFillingArcs (paths q.1.1 q.2) (U q.1.1 q.2 q.1.2.val) q.1.2.val).Adj u v →
    s(x,y) = s(u,v) → p = q
  reserves_disjoint : ∀ e c j (i : Fin t) x y,
    (specialPathFillingArcs (paths c j) (U c j i.val) i.val).Adj x y → s(gL e,gR e) ≠ s(x,y)

/-- Assemble one family of the special factors of §5.1.5. Both sets
of real edges retain their physical identities and are disjoint as
unordered edges, including across the augmentation and filling
reserves. The loop over rounds uses independent copies of the
auxiliary arcs. -/
theorem exists_canonical_special_factors_of_augmentation_matrices
    [Fintype V] [DecidableEq V] [Nonempty V] {h f ℓ s : ℕ}
    (hf : 2 ≤ f) (hℓ : 0 < ℓ) (hCycle : 3 ≤ f*(2*ℓ))
    (C : Fin h × Fin (f*(2*ℓ)) → Finset V) (core : Finset V)
    (aug : V → V → Prop) [DecidableRel aug] (G : Digraph V)
    (H : (Fin h × Fin f) × (Fin s × Fin 2) → Fin ℓ → Fin ℓ → ℕ)
    (blocked : (Fin h × Fin f) × (Fin s × Fin 2) → Finset V)
    (b forbidden cap n r : ℕ) (ε η d a : ℝ)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hSub : ∀ i, C i ⊆ core) (hCover : ∀ v ∈ core, ∃ i, v ∈ C i)
    (hn : 0 < n) (hSize : ∀ i, (C i).card = n)
    (hCap : 0 < cap) (hAugBudget : 4*s*b ≤ forbidden*cap)
    (hBlocked : ∀ j, (blocked j).card ≤ b)
    (hRoomL : b+forbidden ≤ n)
    (hReserves : ∀ x y, aug x y → ¬ G.Adj x y ∧ ¬ G.Adj y x)
    (hη : 0 < η) (hηOne : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hFillBudget : (s:ℝ) ≤ a*((n:ℝ)*η))
    (hGap : 2*η < d) (hr : 0 < r) (hCut : (n:ℝ)*η ≤ (r:ℝ))
    (hMargin : (r:ℝ)+(b:ℝ) ≤ (d-η)*(n:ℝ)) :
    let A := canonicalSpecialCluster (by omega : 0 < f) (by omega : 0 < 2*ℓ) C
    let left (j : (Fin h × Fin f) × (Fin s × Fin 2)) (x : Fin ℓ) :=
      A j.1 (2*x.val + if j.2.2 = 0 then 0 else 2)
    let right (j : (Fin h × Fin f) × (Fin s × Fin 2)) (y : Fin ℓ) := A j.1 (2*y.val+1)
    (∀ j x, (left j x ∩ blocked j).card + ∑ y, H j x y = b) →
    (∀ j y, (right j y ∩ blocked j).card + ∑ x, H j x y = b) →
    (∀ j x y, 0 < H j x y → ∀ v ∈ left j x, v ∉ blocked j →
      b + forbidden + cap ≤ ((right j y).filter (aug v)).card) →
    (∀ c i, i < 2*ℓ → IsLowerSuperregularPair G ε d (A c i) (A c (i+1))) →
    let M j := embeddedAugmentationMatrix (canonicalAugmentationLeft j.1 j.2.2)
      (canonicalAugmentationRight j.1) (H j)
    let requests j := @Finset.filter (ScheduledAugmentationRequest M) (fun e => e.1 = j)
      (Classical.decPred _) univ
    Nonempty (SpecialFactorReserveRealization A core aug G (fun c j u => blocked (c,j,u))
      (fun e : ScheduledAugmentationRequest M => e.1) (fun c j u => requests (c,j,u))
      (2*ℓ) n b cap) := by
  classical
  intro A left right hRows hCols hRoomR hPairs M requests
  have hfPos : 0 < f := by omega
  have hRoomClusters (i : Fin h × Fin (f*(2*ℓ))) : b+forbidden ≤ (C i).card := by
    rw [hSize i]
    exact hRoomL
  have hAugExist := exists_canonical_augmentation_of_interval_matrices hfPos hℓ C aug H blocked
    b forbidden cap hCap hAugBudget hC hBlocked hRoomClusters hRows hCols hRoomR
  refine Exists.elim hAugExist (fun gL h => Exists.elim h (fun gR h => ?_))
  have hAug := h.1
  have hFresh := h.2.1
  have hLoad := h.2.2.1
  have hL := h.2.2.2.1
  have hR := h.2.2.2.2
  let coveredL c j u := blocked (c,j,u) ∪ (requests (c,j,u)).image gL
  let coveredR c j u := blocked (c,j,u) ∪ (requests (c,j,u)).image gR
  let U c j i := A c i ∩ (if i % 2 = 0 then coveredL c j 0 else coveredR c j 1)
  let W c j i := A c (i+1) ∩ (if i % 2 = 0 then coveredR c j 0 else coveredL c j 1)
  obtain ⟨hU,hW,hCounts⟩ := canonical_augmented_occupied_sets A coveredL coveredR b
    (fun c j u x => hL (c,j,u) x) (fun c j u x => hR (c,j,u) x)
  have htPos : 0 < 2*ℓ := by omega
  have hPaths := exists_canonical_special_factors
    hf htPos hCycle C core G U W n r b ε η d a hC hSub hCover hn hSize
    hη hηOne ha hd hTol hFillBudget hGap hr hCut hMargin
    (fun c j i _ => hU c j i) (fun c j i _ => hW c j i)
    (fun c j i hi => ⟨(hCounts c j i hi).1.trans (hCounts c j i hi).2.symm,
      (hCounts c j i hi).1.le⟩) hPairs
  refine Exists.elim hPaths (fun P hP => ?_)
  have hSteps := hP.1
  have hRegular := hP.2.1
  have hFill := hP.2.2.1
  have hSeparate := hP.2.2.2
  refine ⟨{
    gL := gL
    gR := gR
    aug_edges := hAug
    aug_fresh := hFresh
    aug_cap := hLoad
    U := U
    W := W
    source_occupied := fun _ _ _ => rfl
    target_occupied := fun _ _ _ => rfl
    counts := hCounts
    paths := P
    preserves_occupied := hSteps
    regular := hRegular
    fill_in_reserve := fun c j i => hFill ((c,i),j)
    fill_fresh := hSeparate
    reserves_disjoint := ?_
  }⟩
  intro e c j i x y hReal he
  have hIn := hFill ((c,i),j) hReal
  obtain ⟨hForward,hReverse⟩ := hReserves _ _ (hAug e).1
  rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact hForward (hx.symm ▸ hy.symm ▸ hIn)
  · exact hReverse (hx.symm ▸ hy.symm ▸ hIn)

/-- Use explicit sufficient quantitative margins for both reserves
instead of assuming the integer and residual parameters separately. -/
theorem exists_canonical_special_factors_of_superregular_reserves
    [Fintype V] [DecidableEq V] [Nonempty V] {h f ℓ s : ℕ}
    (hf : 2 ≤ f) (hℓ : 0 < ℓ) (hCycle : 3 ≤ f*(2*ℓ))
    (C : Fin h × Fin (f*(2*ℓ)) → Finset V) (core : Finset V)
    (D G : Digraph V)
    (H : (Fin h × Fin f) × (Fin s × Fin 2) → Fin ℓ → Fin ℓ → ℕ)
    (blocked : (Fin h × Fin f) × (Fin s × Fin 2) → Finset V)
    (b n : ℕ) (ε d : ℝ)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hSub : ∀ i, C i ⊆ core) (hCover : ∀ v ∈ core, ∃ i, v ∈ C i)
    (hn : 0 < n) (hSize : ∀ i, (C i).card = n)
    (hBlocked : ∀ j, (blocked j).card ≤ b)
    (hReserves : ∀ x y, D.Adj x y → ¬ G.Adj x y ∧ ¬ G.Adj y x)
    (hd : 0 < d) (hdOne : d ≤ 1) (hLarge : 200 ≤ d*n)
    (hLocal : (b:ℝ) ≤ d*n/100) (hGlobal : (s:ℝ)*b ≤ d^3*(n:ℝ)^2/80000)
    (hε : ε ≤ d/64) (hRounds : (s:ℝ) ≤ d^2*n/512) :
    let A := canonicalSpecialCluster (by omega : 0 < f) (by omega : 0 < 2*ℓ) C
    let left (j : (Fin h × Fin f) × (Fin s × Fin 2)) (x : Fin ℓ) :=
      A j.1 (2*x.val + if j.2.2 = 0 then 0 else 2)
    let right (j : (Fin h × Fin f) × (Fin s × Fin 2)) (y : Fin ℓ) := A j.1 (2*y.val+1)
    (∀ j x, (left j x ∩ blocked j).card + ∑ y, H j x y = b) →
    (∀ j y, (right j y ∩ blocked j).card + ∑ x, H j x y = b) →
    (∀ j x y, 0 < H j x y → IsLowerSuperregularPair D ε d (left j x) (right j y)) →
    (∀ c i, i < 2*ℓ → IsLowerSuperregularPair G ε d (A c i) (A c (i+1))) →
    let M j := embeddedAugmentationMatrix (canonicalAugmentationLeft j.1 j.2.2)
      (canonicalAugmentationRight j.1) (H j)
    let requests j := @Finset.filter (ScheduledAugmentationRequest M) (fun e => e.1 = j)
      (Classical.decPred _) univ
    ∃ cap : ℕ, Nonempty (SpecialFactorReserveRealization A core D.Adj G (fun c j u => blocked (c,j,u))
      (fun e : ScheduledAugmentationRequest M => e.1) (fun c j u => requests (c,j,u))
      (2*ℓ) n b cap) := by
  classical
  intro A left right hRows hCols hAugPairs hFillPairs M requests
  obtain ⟨forbidden,cap,hCap,hAugBudget,hRoomL,hRoomR⟩ :=
    exists_special_factor_augmentation_margins s b n d hd hdOne hLarge hLocal hGlobal
  obtain ⟨η,a,r,hη,hηOne,ha,hTol,hBudget,hGap,hr,hCut,hMargin⟩ :=
    exists_special_factor_filling_margins s b n ε d hd hdOne hLarge hLocal hε hRounds
  refine ⟨cap,?_⟩
  exact exists_canonical_special_factors_of_augmentation_matrices hf hℓ hCycle C core D.Adj G H blocked
    b forbidden cap n r ε η d a hC hSub hCover hn hSize hCap hAugBudget hBlocked hRoomL hReserves
    hη hηOne ha hd.le hTol hBudget hGap hr hCut hMargin hRows hCols
    (fun j x y hp v hv _ => special_factor_augmentation_room_of_superregular D _ _ n
      (b+forbidden+cap) ε d (hSize _) (by linarith only [hε, hd]) hRoomR (hAugPairs j x y hp) v hv)
    hFillPairs

end OverfullWork.ChenShan
