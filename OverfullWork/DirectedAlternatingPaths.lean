module

public import OverfullWork.DirectedReverseRobustExpansion
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section


/-! Alternating layers and simple alternating paths (Lo–Patel, Lemma 4.2). -/
namespace OverfullWork.DirectedAlternatingPaths
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V]

/-- The adjacency used on the edge from position `i` to position `i+1`. -/
def step (D : Digraph V) (i : ℕ) : Digraph V :=
  if i % 2 = 0 then D else reverse D

/-- The layer of possible vertices at position `k+1`. -/
noncomputable def layer (D : Digraph V) (r : ℕ) (u : V) : ℕ → Finset V
  | 0 => univ.filter (D.Adj u)
  | k+1 => neighbourhood (step D (k+1)) r (layer D r u k)

private theorem neighbourhood_eq_univ (D : Digraph V) (S : Finset V) (r t : ℕ)
    (hSize : Fintype.card V ≤ S.card+t) (hDeg : ∀ v, r+t ≤ inDegree D v) :
    neighbourhood D r S = univ := by
  apply eq_univ_of_forall
  intro v
  apply mem_filter.mpr ⟨mem_univ _, ?_⟩
  let A := univ.filter (fun w => D.Adj w v)
  have hA : A.card = inDegree D v := rfl
  have hI : (S ∩ A).card = inNeighbours D S v := by
    congr 1
    ext w
    simp [A]
  have hSum := card_union_add_card_inter S A
  have hUpper := card_le_univ (S ∪ A)
  have hDegree := hDeg v
  omega

private theorem layer_growth (D : Digraph V) {r t : ℕ} (u : V)
    (hRobust : ∀ i, IsRobustAt (step D i) r t)
    (hDegree : ∀ i v, r+t ≤ inDegree (step D i) v)
    (hStart : t ≤ outDegree D u) (k : ℕ) :
    layer D r u k = univ ∨ t+k*r ≤ (layer D r u k).card := by
  induction k with
  | zero => exact Or.inr (by simpa [layer, outDegree] using hStart)
  | succ k ih =>
    by_cases hSize : Fintype.card V ≤ (layer D r u k).card+t
    · exact Or.inl (neighbourhood_eq_univ _ _ r t hSize (hDegree (k+1)))
    · have hLower := ih.resolve_left (fun h => hSize (by simp [h]))
      have hGrow := hRobust (k+1) (layer D r u k) (by omega) (by omega)
      exact Or.inr (by rw [Nat.succ_mul]; change _ ≤ (neighbourhood _ _ _).card; omega)

private theorem extract (D : Digraph V) (r : ℕ) (u : V) (k : ℕ) :
    ∀ (Z : Finset V) (v : V), u ∉ Z → v ∉ Z → u ≠ v →
      Z.card+k+2 ≤ r → v ∈ layer D r u k →
      ∃ f : Fin (k+2) → V, Function.Injective f ∧ f 0 = u ∧ f (Fin.last (k+1)) = v ∧
        (∀ i : Fin (k+1), (step D i).Adj (f i.castSucc) (f i.succ)) ∧
        ∀ i, f i ∉ Z := by
  induction k with
  | zero =>
    intro Z v hu hv huv _ hLayer
    have hEdge : D.Adj u v := (mem_filter.mp hLayer).2
    refine ⟨Fin.snoc (fun _ : Fin 1 => u) v, ?_, by simp, Fin.snoc_last .., ?_, ?_⟩
    · exact Fin.snoc_injective_iff.mpr
        ⟨fun _ _ _ => Subsingleton.elim _ _, by simpa using huv.symm⟩
    · intro i
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [step, Fin.snoc, Fin.lastCases] using hEdge
    · intro i
      induction i using Fin.lastCases <;> simpa using ‹_ ∉ Z›
  | succ k ih =>
    intro Z v hu hv huv hBudget hLayer
    let A := (layer D r u k).filter (fun w => (step D (k+1)).Adj w v)
    let B := insert u (insert v Z)
    have hA : r ≤ A.card := (mem_filter.mp hLayer).2
    have hB : B.card ≤ Z.card+2 :=
      (card_insert_le _ _).trans (Nat.add_le_add_right (card_insert_le _ _) _)
    have hPos : 0 < (A \ B).card := by
      have h := card_le_card_sdiff_add_card (s := A) (t := B)
      omega
    obtain ⟨w, hw⟩ := card_pos.mp hPos
    obtain ⟨hwA, hwB⟩ := mem_sdiff.mp hw
    obtain ⟨hwLayer, hwEdge⟩ := mem_filter.mp hwA
    have hw' : w ≠ u ∧ w ≠ v ∧ w ∉ Z := by simpa [B] using hwB
    have hZ' := card_insert_le v Z
    obtain ⟨f, hf, hFirst, hLast, hEdges, hAvoid⟩ :=
      ih (insert v Z) w (by simp [huv, hu]) (by simp [hw'.2.1, hw'.2.2])
        hw'.1.symm (by omega) hwLayer
    refine ⟨Fin.snoc f v, Fin.snoc_injective_iff.mpr ⟨hf, ?_⟩,
      by simpa using hFirst, by simp, ?_, ?_⟩
    · rintro ⟨i, rfl⟩
      exact hAvoid i (mem_insert_self _ _)
    · intro i
      induction i using Fin.lastCases with
      | last => simpa [Fin.succ_last, hLast] using hwEdge
      | cast j =>
        simpa only [Fin.val_castSucc, Fin.snoc_castSucc, ← Fin.castSucc_succ]
          using hEdges j
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hv
      | cast j => simpa using (fun hz => hAvoid j (mem_insert_of_mem hz) : f j ∉ Z)

/-- The simple alternating path of Lo–Patel Lemma 4.2, with an explicit
forbidden set and a number of internal vertices divisible by four. -/
theorem exists_alternating_path_avoiding (D : Digraph V) {r t : ℕ}
    (hr : 0 < r) (hRobust : ∀ i, IsRobustAt (step D i) r t)
    (hDegree : ∀ i v, r+t ≤ inDegree (step D i) v)
    (Z : Finset V) (u v : V) (hu : u ∉ Z) (hv : v ∉ Z) (huv : u ≠ v)
    (hBudget : Z.card+Fintype.card V/r+8 ≤ r) :
    ∃ k, k % 4 = 0 ∧ k+2 ≤ Fintype.card V/r+8 ∧
      ∃ f : Fin (k+2) → V, Function.Injective f ∧ f 0 = u ∧ f (Fin.last (k+1)) = v ∧
        (∀ i : Fin (k+1), (step D i).Adj (f i.castSucc) (f i.succ)) ∧
        ∀ i, f i ∉ Z := by
  let q := Fintype.card V/r
  let k := 4*((q+2)/4+1)
  have hk : q+2 < k ∧ k ≤ q+6 ∧ k % 4 = 0 := by omega
  have hStart : t ≤ outDegree D u := by
    have hd := hDegree 1 u
    change r+t ≤ outDegree D u at hd
    omega
  have hDiv := Nat.lt_mul_div_succ (Fintype.card V) hr
  have hGrow : Fintype.card V < t+(k-1)*r := by
    have hMul := Nat.mul_le_mul_right r (show q+1 ≤ k-1 by omega)
    change Fintype.card V < r*(q+1) at hDiv
    rw [Nat.mul_comm r (q+1)] at hDiv
    omega
  have hFull := (layer_growth D u hRobust hDegree hStart (k-1)).resolve_right
    (fun h => by have := card_le_univ (layer D r u (k-1)); omega)
  have hNext := neighbourhood_eq_univ (step D k) (layer D r u (k-1)) r t
    (by simp [hFull]) (hDegree k)
  have hkEq : k-1+1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hk.1))
  have hLayer : v ∈ layer D r u k := by
    conv_lhs => rw [← hkEq]
    change v ∈ neighbourhood (step D (k-1+1)) r (layer D r u (k-1))
    rw [hkEq, hNext]
    exact mem_univ _
  exact ⟨k, hk.2.2, by omega, extract D r u k Z v hu hv huv (by omega) hLayer⟩

/-- One-sided expansion suffices for constructing the alternating path.
The same threshold and window are used at every step after reversal. -/
theorem exists_alternating_path_of_out_robust (D : Digraph V) {r s t : ℕ}
    (hs : 0 < s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hRevBudget : s*Fintype.card V ≤ r*(r-s))
    (hIn : ∀ v, 2*t+s ≤ inDegree D v) (hOut : ∀ v, 2*t+s ≤ outDegree D v)
    (hRobust : IsRobustAt D r t)
    (Z : Finset V) (u v : V) (hu : u ∉ Z) (hv : v ∉ Z) (huv : u ≠ v)
    (hBudget : Z.card+Fintype.card V/s+8 ≤ s) :
    ∃ k, k % 4 = 0 ∧ k+2 ≤ Fintype.card V/s+8 ∧
      ∃ f : Fin (k+2) → V, Function.Injective f ∧ f 0 = u ∧ f (Fin.last (k+1)) = v ∧
        (∀ i : Fin (k+1), (step D i).Adj (f i.castSucc) (f i.succ)) ∧
        ∀ i, f i ∉ Z := by
  apply exists_alternating_path_avoiding D (t := 2*t) hs _ _ Z u v hu hv huv hBudget
  · intro i
    by_cases hi : i % 2 = 0
    · rw [step, if_pos hi]
      intro S hlo hhi
      have hGrowth := hRobust S (by omega) (by omega)
      have hSub : neighbourhood D r S ⊆ neighbourhood D s S := by
        intro x hx
        exact mem_filter.mpr ⟨mem_univ _, hsr.trans (mem_filter.mp hx).2⟩
      exact (Nat.add_le_add_left hsr _).trans (hGrowth.trans (card_le_card hSub))
    · rw [step, if_neg hi]
      exact reverse_robust_of_robust D hs hsr hrt hRevBudget
        (fun w => (Nat.le_add_right _ _).trans (hIn w)) hRobust
  · intro i w
    by_cases hi : i % 2 = 0
    · simpa [step, hi, Nat.add_comm] using hIn w
    · rw [step, if_neg hi, Nat.add_comm]
      exact hOut w

end OverfullWork.DirectedAlternatingPaths
