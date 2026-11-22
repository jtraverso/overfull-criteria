module

public import OverfullWork.HamiltonPathClosure
public import OverfullWork.ColouredLayerSum

@[expose] public section


/-! # Close the entire boundary path packing without exceeding any copy

Boundary copies are counted by the actual stub bijections. Ordinary
edges are used at most once by disjointness of the packed paths. The
central bundle contributes one copy per layer.
-/
namespace OverfullWork.HeavyPairColouredBatch
open SimpleGraph Finset HeavyPairBoundary HamiltonPathClosure CanonicalPairTriangle PathGraphRealization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

variable {M : MultiGraph V} {a b : V} {q : ℕ}
variable (f : Fin q ≃ (Σ w : outside a b, Fin (M.mult s(a,w.val))))
variable (g : Fin q ≃ (Σ w : outside a b, Fin (M.mult s(b,w.val))))
variable (s : DenseBatchPathPacking.Packing (M.supportGraph.induce (outside a b : Set V)) q 1
    (fun j _ => (f j).1) (fun j _ => (g j).1))

noncomputable def batch (hab : a ≠ b) : MultiGraph V :=
  sumCopies univ (fun j => layer (s.paths j 0) hab)

theorem batch_regular (hab : a ≠ b) (hn : 2 ≤ Fintype.card ↥(outside a b)) :
    (batch f g s hab).IsRegularOfDegree (2*q) := by
  have hreg := ColouredLayerSum.regular (fun j => layer (s.paths j 0) hab) (fun j =>
    layer_regular _ hab (singleton_round_hamiltonian s j)
      (hamiltonian_endpoints_ne _ (singleton_round_hamiltonian s j) hn))
  simpa only [batch, Nat.mul_comm] using hreg

theorem batch_colourable (hab : a ≠ b) (hn : 2 ≤ Fintype.card ↥(outside a b))
    (heven : Even (Fintype.card V)) : Nonempty ((batch f g s hab).EdgeColoring (2*q)) := by
  have hcol : ∀ j, Nonempty ((layer (s.paths j 0) hab).EdgeColoring 2) := fun j =>
    layer_colourable _ hab (singleton_round_hamiltonian s j)
      (hamiltonian_endpoints_ne _ (singleton_round_hamiltonian s j) hn) heven
  let C := fun j => Classical.choice (hcol j)
  have hc := ColouredLayerSum.colouring (fun j => layer (s.paths j 0) hab) C
  exact ⟨by simpa only [batch, Nat.mul_comm] using hc⟩

theorem layer_left (hab : a ≠ b) (j : Fin q) (w : outside a b) :
    (layer (s.paths j 0) hab).mult s(a,w.val) = if w = (f j).1 then 1 else 0 := by
  apply EvenPathClosure.closure_mult_left
  rw [MultiGraph.degree_ofSimpleGraph]
  apply degree_outside
  intro ha
  have hh := (ambientPath_support _ (singleton_round_hamiltonian s j) a).mp ha
  exact ((mem_outside a b a).mp hh).1 rfl

theorem layer_right (hab : a ≠ b) (j : Fin q) (w : outside a b) :
    (layer (s.paths j 0) hab).mult s(b,w.val) = if w = (g j).1 then 1 else 0 := by
  apply EvenPathClosure.closure_mult_right
  rw [MultiGraph.degree_ofSimpleGraph]
  apply degree_outside
  intro hb
  have hh := (ambientPath_support _ (singleton_round_hamiltonian s j) b).mp hb
  exact ((mem_outside a b b).mp hh).2 rfl

theorem batch_left (hab : a ≠ b) (w : outside a b) :
    (batch f g s hab).mult s(a,w.val) = M.mult s(a,w.val) := by
  change (∑ j, (layer (s.paths j 0) hab).mult s(a,w.val)) = _
  simp_rw [layer_left f g s hab]
  simpa only [eq_comm] using ColouredLayerSum.enumeration_fiber_sum
    (fun w : outside a b => M.mult s(a,w.val)) f w

theorem batch_right (hab : a ≠ b) (w : outside a b) :
    (batch f g s hab).mult s(b,w.val) = M.mult s(b,w.val) := by
  change (∑ j, (layer (s.paths j 0) hab).mult s(b,w.val)) = _
  simp_rw [layer_right f g s hab]
  simpa only [eq_comm] using ColouredLayerSum.enumeration_fiber_sum
    (fun w : outside a b => M.mult s(b,w.val)) g w

theorem batch_pair (hab : a ≠ b) : (batch f g s hab).mult s(a,b) = q := by
  change (∑ j, (layer (s.paths j 0) hab).mult s(a,b)) = _
  have hpoint : ∀ j, (layer (s.paths j 0) hab).mult s(a,b) = 1 := by
    intro j
    apply EvenPathClosure.closure_mult_pair
    rw [MultiGraph.degree_ofSimpleGraph]
    apply degree_outside
    intro ha
    have hh := (ambientPath_support _ (singleton_round_hamiltonian s j) a).mp ha
    exact ((mem_outside a b a).mp hh).1 rfl
  simp only [hpoint, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem batch_ordinary_le (hab : a ≠ b) (x y : outside a b) :
    (batch f g s hab).mult s(x.val,y.val) ≤ M.mult s(x.val,y.val) := by
  let P : Fin q → MultiGraph V := fun j =>
    MultiGraph.ofSimpleGraph (pathGraph (ambientPath (s.paths j 0)))
  have hpoint : ∀ j, (layer (s.paths j 0) hab).mult s(x.val,y.val) = (P j).mult s(x.val,y.val) :=
    fun j => EvenPathClosure.closure_mult_ordinary _ a b hab _ _ x y
  change (∑ j, (layer (s.paths j 0) hab).mult s(x.val,y.val)) ≤ _
  simp_rw [hpoint]
  have hcap : ∀ j, (P j).mult s(x.val,y.val) ≤ 1 := by
    intro j
    change (if s(x.val,y.val) ∈ (pathGraph (ambientPath (s.paths j 0))).edgeSet then 1 else 0) ≤ 1
    split_ifs <;> omega
  have hadj : ∀ j, (P j).mult s(x.val,y.val) ≠ 0 →
      (pathGraph (s.paths j 0)).Adj x y := by
    intro j hj
    apply (ambientPath_adj_iff _ x y).mp
    by_contra hn
    apply hj
    change (if s(x.val,y.val) ∈ (pathGraph (ambientPath (s.paths j 0))).edgeSet then 1 else 0) = 0
    simp only [mem_edgeSet, if_neg hn]
  have hone : (∑ j, (P j).mult s(x.val,y.val)) ≤ 1 := by
    apply sum_le_one_iff.mpr
    intro j k _ _ hj hk
    have hjk : j = k := by
      by_contra hne
      have hd := s.rounds_disjoint j k hne
      have h1 : (pathUnion (s.paths j)).Adj x y := (pathUnion_adj_iff _).mpr ⟨0,hadj j hj⟩
      have h2 : (pathUnion (s.paths k)).Adj x y := (pathUnion_adj_iff _).mpr ⟨0,hadj k hk⟩
      exact (disjoint_iff_inf_le.mp hd) ⟨h1,h2⟩
    exact ⟨hjk, by have hc := hcap j; omega⟩
  by_cases hM : 0 < M.mult s(x.val,y.val)
  · exact hone.trans (by omega)
  · have hzero : ∀ j, (P j).mult s(x.val,y.val) = 0 := by
      intro j
      by_contra hj
      have he := le_original (s.paths j 0) (hadj j hj)
      exact hM he
    simp only [hzero, sum_const_zero, Nat.zero_le]

theorem batch_le (hab : a ≠ b) (hq : q ≤ M.mult s(a,b)) :
    ∀ t, (batch f g s hab).mult t ≤ M.mult t := by
  intro t
  induction t using Sym2.inductionOn with
  | hf x y =>
    by_cases hxy : x = y
    · subst y
      rw [(batch f g s hab).loopless _ (by simp)]
      exact Nat.zero_le _
    by_cases hxa : x = a
    · subst x
      by_cases hyb : y = b
      · subst y; rw [batch_pair f g s hab]; exact hq
      · rw [batch_left f g s hab ⟨y,(mem_outside a b y).mpr ⟨Ne.symm hxy,hyb⟩⟩]
    by_cases hxb : x = b
    · subst x
      by_cases hya : y = a
      · subst y
        rw [show s(b,a) = s(a,b) from Sym2.eq_swap, batch_pair f g s hab]
        exact hq
      · rw [batch_right f g s hab ⟨y,(mem_outside a b y).mpr ⟨hya,Ne.symm hxy⟩⟩]
    by_cases hya : y = a
    · subst y
      rw [show s(x,a) = s(a,x) from Sym2.eq_swap,
        batch_left f g s hab ⟨x,(mem_outside a b x).mpr ⟨hxa,hxb⟩⟩]
    by_cases hyb : y = b
    · subst y
      rw [show s(x,b) = s(b,x) from Sym2.eq_swap,
        batch_right f g s hab ⟨x,(mem_outside a b x).mpr ⟨hxa,hxb⟩⟩]
    exact batch_ordinary_le f g s hab
      ⟨x,(mem_outside a b x).mpr ⟨hxa,hxb⟩⟩ ⟨y,(mem_outside a b y).mpr ⟨hya,hyb⟩⟩

end OverfullWork.HeavyPairColouredBatch
