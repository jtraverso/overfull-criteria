module

public import OverfullWork.InitialMiddleCopies

@[expose] public section


/-! # Exact internal-plus-middle graph and protected triangle

All original internal copies are retained. Selected crossing centre
copies form a genuine submultigraph. The initial protected selection
proves CMS (5.8) for every subsequent middle-star addition.
-/
namespace OverfullWork.MiddleCopyGraph
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

def graph (M : MultiGraph V) (A : Finset V) (a : V) (f : V → ℕ) (hf : f a = 0) : MultiGraph V :=
  (M.internalPart A).addCopies (MultiGraph.starCopies a f hf)

theorem centre_degree (M : MultiGraph V) (A : Finset V) (a : V)
    (f : V → ℕ) (hf : f a = 0) (ha : a ∈ A) :
    (graph M A a f hf).degree a = M.degreeInto A a + ∑ v, f v := by
  rw [graph,MultiGraph.degree_addCopies,MultiGraph.degree_internalPart,if_pos ha,
    MultiGraph.degree_starCopies_center]

theorem other_degree (M : MultiGraph V) (A : Finset V) (a v : V)
    (f : V → ℕ) (hf : f a = 0) (hv : v ≠ a) :
    (graph M A a f hf).degree v =
      (if v ∈ A then M.degreeInto A v else M.degreeInto Aᶜ v)+f v := by
  rw [graph,MultiGraph.degree_addCopies,MultiGraph.degree_internalPart,
    MultiGraph.degree_starCopies_other _ _ _ _ hv]

theorem le_original (M : MultiGraph V) (A : Finset V) (a : V) (ha : a ∈ A)
    (f : V → ℕ) (hf : f a = 0) (hcap : ∀ v, f v ≤ M.mult s(a,v))
    (hCross : ∀ v ∈ A, f v = 0) : ∀ t, (graph M A a f hf).mult t ≤ M.mult t := by
  intro t
  induction t using Sym2.inductionOn with
  | hf u v =>
    change (M.internalPart A).mult s(u,v)+(MultiGraph.starCopies a f hf).mult s(u,v) ≤ _
    rw [MultiGraph.internalPart_mult,MultiGraph.starCopies_mult]
    by_cases hua : u = a
    · subst u
      rw [if_pos rfl]
      by_cases hv : v ∈ A
      · simp [ha,hv,hCross v hv]
      · simpa [ha,hv] using hcap v
    rw [if_neg hua]
    by_cases hva : v = a
    · subst v
      rw [if_pos rfl]
      by_cases hu : u ∈ A
      · simp [ha,hu,hCross u hu]
      · simpa [ha,hu,Sym2.eq_swap] using hcap u
    rw [if_neg hva,add_zero]
    split_ifs <;> omega

theorem crossing_mult (M : MultiGraph V) (A : Finset V) (a b : V)
    (f : V → ℕ) (hf : f a = 0) (ha : a ∈ A) (hb : b ∉ A) :
    (graph M A a f hf).mult s(a,b) = f b := by
  change (M.internalPart A).mult s(a,b)+(MultiGraph.starCopies a f hf).mult s(a,b) = _
  rw [MultiGraph.internalPart_mult,MultiGraph.starCopies_mult]
  simp [ha,hb]

theorem opposite_mult (M : MultiGraph V) (A : Finset V) (a b w : V)
    (f : V → ℕ) (hf : f a = 0) (ha : a ∈ A) (hb : b ∉ A) (hw : w ∉ A) :
    (graph M A a f hf).mult s(b,w) = M.mult s(b,w) := by
  have hba : b ≠ a := fun he => hb (he ▸ ha)
  have hwa : w ≠ a := fun he => hw (he ▸ ha)
  change (M.internalPart A).mult s(b,w)+(MultiGraph.starCopies a f hf).mult s(b,w) = _
  rw [MultiGraph.internalPart_mult,MultiGraph.starCopies_mult]
  simp [hb,hw,hba,hwa]

theorem triangle_count (M : MultiGraph V) (A : Finset V) (a b w : V)
    (f : V → ℕ) (hf : f a = 0) (ha : a ∈ A) (hb : b ∉ A) (hw : w ∉ A) (hbw : b ≠ w) :
    (graph M A a f hf).edgesWithin {a,b,w} = M.mult s(b,w)+f b+f w := by
  have hab : a ≠ b := fun he => hb (he ▸ ha)
  have haw : a ≠ w := fun he => hw (he ▸ ha)
  have ht := CriticalCentreTriples.triple_internal (graph M A a f hf) a b w hab haw hbw
  rw [MultiGraph.twiceInternal_eq,crossing_mult M A a b f hf ha hb,
    crossing_mult M A a w f hf ha hw,opposite_mult M A a b w f hf ha hb hw] at ht
  omega

theorem protected_triangle (M : MultiGraph V) (A H : Finset V) (a b w : V)
    (s : InitialMiddleCopies.Selection M A H a b w)
    (ha : a ∈ A) (hb : b ∉ A) (hw : w ∉ A) (hbw : b ≠ w)
    (g : V → ℕ) (hg : g a = 0) :
    let f := fun v => s.count v+g v
    let hf : f a = 0 := by dsimp only [f];rw [s.centre_zero ha,hg]
    (graph M A a f hf).edgesWithin {a,b,w} ≤ (graph M A a f hf).degree a := by
  dsimp only
  rw [triangle_count _ _ _ _ _ _ _ ha hb hw hbw,centre_degree _ _ _ _ _ ha,
    sum_add_distrib,s.second_zero,s.exception_zero,zero_add,zero_add]
  have hbudget := s.protection_budget
  have hsub : ({b,w} : Finset V) ⊆ univ := subset_univ _
  have hs := sum_le_sum_of_subset_of_nonneg hsub (f := g) (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hbw] at hs
  omega

end OverfullWork.MiddleCopyGraph
