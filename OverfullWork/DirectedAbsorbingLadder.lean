module

public import OverfullWork.DirectedAlternatingPaths
public import OverfullWork.DirectedDisjointShortPaths

@[expose] public section


/-! An actual ladder, assembled as in Lo–Patel Definition 4.3 and Lemma 4.9. -/
namespace OverfullWork.DirectedAbsorbingLadder
open Finset DirectedRobustExpansion DirectedAlternatingPaths DirectedRobustShortPaths
open DirectedListRoutes
open scoped Classical
variable {V : Type*}

def left {q : ℕ} (i : Fin q) : Fin (4*q+2) := ⟨2*i.val+1, by have := i.isLt; omega⟩
def right {q : ℕ} (i : Fin q) : Fin (4*q+2) := ⟨4*q-2*i.val, by omega⟩

structure Ladder (D : Digraph V) (u v : V) (q : ℕ) where
  spine : Fin (4*q+2) ↪ V
  source : spine 0 = u
  target : spine (Fin.last (4*q+1)) = v
  arcs : ∀ i : Fin (4*q+1), (step D i).Adj (spine i.castSucc) (spine i.succ)
  tail : Fin q → List V
  routes : ∀ i, Route D (spine (left i)) (spine (right i)) (tail i)
  simple : ∀ i, (spine (left i) :: tail i).Nodup
  disjoint : ∀ i j, i ≠ j → List.Disjoint (spine (left i) :: tail i) (spine (left j) :: tail j)
  meets_spine : ∀ i w, w ∈ spine (left i) :: tail i → w ∈ Set.range spine →
    w = spine (left i) ∨ w = spine (right i)

noncomputable def Ladder.vertices {D : Digraph V} {u v : V} {q : ℕ}
    (A : Ladder D u v q) : Finset V :=
  (univ.image A.spine) ∪ univ.biUnion (fun i => (A.spine (left i) :: A.tail i).toFinset)

private theorem Ladder.card_vertices_le {D : Digraph V} {u v : V} {q L : ℕ}
    (A : Ladder D u v q) (hLen : ∀ i, (A.spine (left i) :: A.tail i).length ≤ L) :
    A.vertices.card ≤ (4*q+2)+q*L := by
  have hSpine : (univ.image A.spine).card ≤ 4*q+2 := card_image_le.trans (by simp)
  have hTails : (univ.biUnion (fun i => (A.spine (left i) :: A.tail i).toFinset)).card ≤ q*L := by
    apply card_biUnion_le.trans
    simpa using (sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin q))) =>
      (List.toFinset_card_le _).trans (hLen i)) :
      (∑ i : Fin q, (A.spine (left i) :: A.tail i).toFinset.card) ≤ ∑ _i : Fin q, L)
  exact (card_union_le _ _).trans (Nat.add_le_add hSpine hTails)

private theorem left_injective (q : ℕ) : Function.Injective (@left q) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  change 2*i.val+1 = 2*j.val+1 at h
  omega

private theorem right_injective (q : ℕ) : Function.Injective (@right q) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  have hi := i.isLt
  have hj := j.isLt
  change 4*q-2*i.val = 4*q-2*j.val at h
  omega

private theorem left_ne_right {q : ℕ} (i j : Fin q) : left i ≠ right j := by
  intro h
  have hj := j.isLt
  have h := congrArg Fin.val h
  change 2*i.val+1 = 4*q-2*j.val at h
  omega

/-- Construct a bounded ladder, with its whole support avoiding `Z`.
The budgets account separately for the alternating spine and the
greedily routed directed paths between its paired odd positions. -/
theorem exists_ladder_avoiding [Fintype V] (D : Digraph V) {r s t r' L : ℕ}
    (hs : 0 < s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hRevBudget : s*Fintype.card V ≤ r*(r-s))
    (hIn : ∀ v, 2*t+s ≤ inDegree D v) (hOut : ∀ v, 2*t+s ≤ outDegree D v)
    (hRobust : IsRobustAt D r t) (hr' : 0 < r')
    (hL : Fintype.card V/r'+4 ≤ L)
    (Z : Finset V) (u v : V) (hu : u ∉ Z) (hv : v ∉ Z) (huv : u ≠ v)
    (hSpineBudget : Z.card+Fintype.card V/s+8 ≤ s)
    (hRouteBudget : Z.card+(Fintype.card V/s+8)+(Fintype.card V/s+8)/4*L+r' ≤ r)
    (hOutBudget : ∀ w, t+Z.card+(Fintype.card V/s+8)+(Fintype.card V/s+8)/4*L ≤ outDegree D w) :
    ∃ q, 4*q+2 ≤ Fintype.card V/s+8 ∧
      ∃ A : Ladder D u v q, A.vertices.card ≤ (4*q+2)+q*L ∧ Disjoint A.vertices Z := by
  obtain ⟨k, hk, hSize, f, hInject, hStart, hEnd, hArc, hAvoid⟩ :=
    exists_alternating_path_of_out_robust D hs hsr hrt hRevBudget hIn hOut hRobust
      Z u v hu hv huv hSpineBudget
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hk
  let M := univ.image f
  have hM : M.card ≤ 4*q+2 := card_image_le.trans (by simp)
  have hq : q ≤ (Fintype.card V/s+8)/4 := by omega
  have hMul := Nat.mul_le_mul_right L hq
  let x : Fin q → V := fun i => f (left i)
  let y : Fin q → V := fun i => f (right i)
  have hMarks : ∀ i, x i ∈ M ∧ y i ∈ M := fun i =>
    ⟨mem_image_of_mem _ (mem_univ (left i)), mem_image_of_mem _ (mem_univ (right i))⟩
  obtain ⟨paths, hPaths, hDisj⟩ := exists_disjoint_short_paths D hRobust hr' hL M x y
    (hInject.comp (left_injective q)) (hInject.comp (right_injective q))
    (fun i j h => left_ne_right i j (hInject h)) hMarks
    (fun w => by have := hIn w; omega) univ Z (fun i _ => ⟨hAvoid _, hAvoid _⟩)
    (by rw [card_univ, Fintype.card_fin]; omega)
    (fun w => by rw [card_univ, Fintype.card_fin]; have := hOutBudget w; omega)
  let A : Ladder D u v q := {
    spine := ⟨f, hInject⟩
    source := hStart
    target := hEnd
    arcs := hArc
    tail := paths
    routes := fun i => (hPaths i (mem_univ _)).1
    simple := fun i => (hPaths i (mem_univ _)).2.1
    disjoint := fun i j => hDisj i (mem_univ _) j (mem_univ _)
    meets_spine := fun i w hw hm => (hPaths i (mem_univ _)).2.2.2 w hw |>.2
      (by simpa [M, Function.Embedding.coeFn_mk] using hm) }
  refine ⟨q, hSize, A, A.card_vertices_le (fun i => (hPaths i (mem_univ _)).2.2.1), ?_⟩
  apply Finset.disjoint_left.mpr
  intro w hw hwZ
  rcases mem_union.mp hw with hSp|hTail
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hSp
    exact hAvoid i hwZ
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hTail
    exact ((hPaths i (mem_univ _)).2.2.2 w (List.mem_toFinset.mp hi)).1 hwZ

end OverfullWork.DirectedAbsorbingLadder
