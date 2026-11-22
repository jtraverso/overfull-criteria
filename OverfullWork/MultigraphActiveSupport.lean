module

public import OverfullWork.SubtypeColouringExtension

@[expose] public section


/-! # Restrict a multiplicity graph to its actual active vertices

The designated anchor is retained even when isolated. Restriction and
extension are exact, so isolated vertices cannot become fake witnesses
in the low-centre-bundle reduction.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

def onVertices (M : MultiGraph V) (S : Finset V) : MultiGraph ↥S where
  mult e := M.mult (Sym2.map Subtype.val e)
  loopless e he := M.loopless _ (he.map)

theorem onVertices_mult (M : MultiGraph V) (S : Finset V) (u v : S) :
    (M.onVertices S).mult s(u,v) = M.mult s(u.val,v.val) := rfl

def activeWith (M : MultiGraph V) (a : V) : Finset V := univ.filter (fun v => v=a ∨ 0 < M.degree v)

theorem mem_activeWith (M : MultiGraph V) (a v : V) :
    v ∈ M.activeWith a ↔ v=a ∨ 0 < M.degree v := by simp [activeWith]

theorem mult_eq_zero_of_degree_zero (M : MultiGraph V) (u v : V) (hu : M.degree u = 0) :
    M.mult s(u,v) = 0 := by
  have hh : M.mult s(u,v) ≤ M.degree u := by
    rw [degree_eq_sum_mult]
    exact single_le_sum (f := fun w => M.mult s(u,w)) (fun _ _ => Nat.zero_le _) (mem_univ v)
  omega

theorem mult_zero_outside_activeWith (M : MultiGraph V) (a u v : V) (hu : u ∉ M.activeWith a) :
    M.mult s(u,v) = 0 := by
  have hz : M.degree u = 0 := by
    have hh := not_congr (M.mem_activeWith a u)
    simp only [not_or,not_lt] at hh
    exact Nat.eq_zero_of_le_zero (hh.mp hu).2
  exact M.mult_eq_zero_of_degree_zero u v hz

theorem extend_activeWith (M : MultiGraph V) (a : V) :
    OverfullWork.SubtypeColouringExtension.extend (M.activeWith a) (M.onVertices (M.activeWith a)) = M := by
  apply ext_mult
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    by_cases hu : u ∈ M.activeWith a
    · by_cases hv : v ∈ M.activeWith a
      · exact OverfullWork.SubtypeColouringExtension.extend_mult _ _ ⟨u,hu⟩ ⟨v,hv⟩
      · rw [show s(u,v) = s(v,u) from Sym2.eq_swap,
          OverfullWork.SubtypeColouringExtension.extend_mult_outside _ _ v u hv,
          M.mult_zero_outside_activeWith a v u hv]
    · rw [OverfullWork.SubtypeColouringExtension.extend_mult_outside _ _ u v hu,
        M.mult_zero_outside_activeWith a u v hu]

theorem onVertices_active_degree (M : MultiGraph V) (a : V) (v : M.activeWith a) :
    (M.onVertices (M.activeWith a)).degree v = M.degree v.val := by
  have hh := OverfullWork.SubtypeColouringExtension.extend_degree (M.activeWith a)
    (M.onVertices (M.activeWith a)) v
  rw [M.extend_activeWith a] at hh
  exact hh.symm

theorem colourable_of_activeWith (M : MultiGraph V) (a : V) (k : ℕ)
    (hc : Nonempty ((M.onVertices (M.activeWith a)).EdgeColoring k)) :
    Nonempty (M.EdgeColoring k) := by
  obtain ⟨C⟩ := hc
  have hh := OverfullWork.SubtypeColouringExtension.extend_colouring _ _ C
  rw [M.extend_activeWith a] at hh
  exact ⟨hh⟩

end SimpleGraph.MultiGraph
