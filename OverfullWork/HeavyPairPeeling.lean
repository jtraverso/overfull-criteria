module

public import OverfullWork.HeavyPairColouredBatch

@[expose] public section


/-! # Actual coloured peeling and the regular separated residue

This completes the initial cycle-removal step of CMS Theorem 4.2,
Case 1 in the proved dense range. The residue has no boundary edges;
factorizing its ordinary component remains a separate task.
-/
namespace OverfullWork.HeavyPairPeeling
open SimpleGraph Finset HeavyPairBoundary HeavyPairColouredBatch
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

structure Certificate (M : MultiGraph V) (d q : ℕ) (a b : V) where
  cover : MultiGraph V
  le_original : ∀ t, cover.mult t ≤ M.mult t
  regular : cover.IsRegularOfDegree (2*q)
  colourable : Nonempty (cover.EdgeColoring (2*q))
  boundary_left : ∀ w : outside a b, cover.mult s(a,w.val) = M.mult s(a,w.val)
  boundary_right : ∀ w : outside a b, cover.mult s(b,w.val) = M.mult s(b,w.val)
  pair_copies : cover.mult s(a,b) = q
  residual_regular : (M.subtractCopies cover).IsRegularOfDegree (d-2*q)

def Certificate.residual {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) : MultiGraph V := M.subtractCopies c.cover

theorem Certificate.residual_boundary_left {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (w : outside a b) : c.residual.mult s(a,w.val) = 0 := by
  change M.mult s(a,w.val) - c.cover.mult s(a,w.val) = 0
  rw [c.boundary_left w, Nat.sub_self]

theorem Certificate.residual_boundary_right {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (w : outside a b) : c.residual.mult s(b,w.val) = 0 := by
  change M.mult s(b,w.val) - c.cover.mult s(b,w.val) = 0
  rw [c.boundary_right w, Nat.sub_self]

theorem Certificate.residual_pair {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (hreg : M.IsRegularOfDegree d)
    (hq : q = d - M.mult s(a,b)) : c.residual.mult s(a,b) = d-2*q := by
  have hk := M.mult_pair_le_degree a b
  rw [hreg a] at hk
  change M.mult s(a,b) - c.cover.mult s(a,b) = _
  rw [c.pair_copies]
  omega

/-- Assemble a coloured cover from the physical packing of the paired
boundary copies. The path constructor can use dense or robust linkage. -/
theorem certificate_of_boundary_packing (M : MultiGraph V) (d : ℕ) (a b : V)
    (hab : a ≠ b) (hreg : M.IsRegularOfDegree d) (heven : Even (Fintype.card V))
    (hCore : 2 ≤ Fintype.card ↥(outside a b))
    (hCopies : d-M.mult s(a,b) ≤ M.mult s(a,b))
    (f : Fin (d-M.mult s(a,b)) ≃ (Σ w : outside a b, Fin (M.mult s(a,w.val))))
    (g : Fin (d-M.mult s(a,b)) ≃ (Σ w : outside a b, Fin (M.mult s(b,w.val))))
    (s : DenseBatchPathPacking.Packing (M.supportGraph.induce (outside a b : Set V))
      (d-M.mult s(a,b)) 1 (fun j _ => (f j).1) (fun j _ => (g j).1)) :
    Nonempty (Certificate M d (d-M.mult s(a,b)) a b) := by
  let H := batch f g s hab
  have hle : ∀ t, H.mult t ≤ M.mult t := batch_le f g s hab hCopies
  have hregular : H.IsRegularOfDegree (2*(d-M.mult s(a,b))) := batch_regular f g s hab hCore
  exact ⟨{
    cover := H
    le_original := hle
    regular := hregular
    colourable := batch_colourable f g s hab hCore heven
    boundary_left := batch_left f g s hab
    boundary_right := batch_right f g s hab
    pair_copies := batch_pair f g s hab
    residual_regular := MultiGraph.regular_subtract _ H hle hreg hregular
  }⟩

/-- The cover and its colouring are outputs of the actual path packing. -/
theorem exists_certificate (D A : MultiGraph V) (d B : ℕ)
    (a b : V) (hab : a ≠ b) (hStar : D.IsStarAt a)
    (hreg : (D.addCopies A).IsRegularOfDegree d)
    (hNo : ¬ (D.addCopies A).HasOverfullSubset d)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B)
    (heven : Even (Fintype.card V)) (hn : 10 ≤ Fintype.card V)
    (hslack : Fintype.card V + 6 * (d - (D.addCopies A).mult s(a,b)) +
      2 * B + 10 ≤ 2 * d) :
    Nonempty (Certificate (D.addCopies A) d (d - (D.addCopies A).mult s(a,b)) a b) := by
  obtain ⟨e,f,⟨s⟩⟩ := exists_boundary_path_packing D A d B a b hab hStar hreg hNo hBudget hn hslack
  have hc := card_outside a b hab
  exact certificate_of_boundary_packing (D.addCopies A) d a b hab hreg heven (by omega)
    (pair_copies_suffice (D.addCopies A) d B hreg a b hslack) f (f.trans e) s

def ordinary (R : MultiGraph V) (a b : V) : MultiGraph ↥(outside a b) where
  mult := Sym2.lift ⟨(fun x y => R.mult s(x.val,y.val)), by
    intro x y
    exact congrArg R.mult Sym2.eq_swap⟩
  loopless t ht := by
    induction t using Sym2.inductionOn with
    | hf x y =>
      have hxy : x = y := Sym2.mk_isDiag_iff.mp ht
      subst y
      exact R.loopless _ (by simp)

theorem ordinary_mult (R : MultiGraph V) (a b : V) (x y : outside a b) :
    (ordinary R a b).mult s(x,y) = R.mult s(x.val,y.val) := rfl

theorem Certificate.ordinary_regular {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (hab : a ≠ b) :
    (ordinary c.residual a b).IsRegularOfDegree (d-2*q) := by
  intro w
  rw [MultiGraph.degree_eq_sum_mult]
  simp only [ordinary_mult]
  have hs := sum_outside_add (fun v => c.residual.mult s(w.val,v)) a b hab
  have ha : c.residual.mult s(w.val,a) = 0 := by
    rw [show s(w.val,a) = s(a,w.val) from Sym2.eq_swap]
    exact c.residual_boundary_left w
  have hb : c.residual.mult s(w.val,b) = 0 := by
    rw [show s(w.val,b) = s(b,w.val) from Sym2.eq_swap]
    exact c.residual_boundary_right w
  rw [ha,hb,add_zero,add_zero,← c.residual.degree_eq_sum_mult] at hs
  exact hs.trans (c.residual_regular w.val)

end OverfullWork.HeavyPairPeeling
