module

public import OverfullWork.MultiplicityLayerColouring
public import OverfullWork.InternalEdges

@[expose] public section


/-! # Construct the saturated-centre branch of CMS Lemma 3.10

Keep min(mu,multiplicity) copies at the centre and all ordinary edges.
Color the bounded-multiplicity part by simple copy levels. The residual
is an actual star and receives a disjoint palette. If every ordinary
centre bundle has at least mu copies, the total palette is d(a)+mu.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

def truncateCentre (M : MultiGraph V) (a : V) (μ : ℕ) : MultiGraph V where
  mult e := if a ∈ e then min (M.mult e) μ else M.mult e
  loopless e he := by rw [M.loopless e he];simp

theorem truncateCentre_le (M : MultiGraph V) (a : V) (μ : ℕ) :
    ∀ e, (M.truncateCentre a μ).mult e ≤ M.mult e := by
  intro e
  dsimp only [truncateCentre]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem truncateCentre_cap (M : MultiGraph V) (a : V) (μ : ℕ)
    (hoff : ∀ u v, u ≠ a → v ≠ a → M.mult s(u,v) ≤ μ) :
    ∀ e, (M.truncateCentre a μ).mult e ≤ μ := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    change (if a ∈ s(u,v) then min (M.mult s(u,v)) μ else M.mult s(u,v)) ≤ μ
    split_ifs with h
    · exact min_le_right _ _
    · have hu : u ≠ a := by intro he;subst u;exact h (by simp)
      have hv : v ≠ a := by intro he;subst v;exact h (by simp)
      exact hoff u v hu hv

theorem truncateCentre_degree (M : MultiGraph V) (a : V) (μ : ℕ)
    (hsat : ∀ v, v ≠ a → μ ≤ M.mult s(a,v)) :
    (M.truncateCentre a μ).degree a = (Fintype.card V-1)*μ := by
  rw [degree_eq_sum_mult]
  have hrow : ∀ v ∈ univ.erase a, (M.truncateCentre a μ).mult s(a,v) = μ := by
    intro v hv
    change (if a ∈ s(a,v) then min (M.mult s(a,v)) μ else M.mult s(a,v)) = μ
    simp only [Sym2.mem_iff,true_or,if_true]
    exact min_eq_right (hsat v (mem_erase.mp hv).1)
  have hz := (M.truncateCentre a μ).loopless s(a,a) (by simp)
  have hh := sum_erase_add univ (fun v => (M.truncateCentre a μ).mult s(a,v)) (mem_univ a)
  rw [hz,add_zero] at hh
  rw [←hh,sum_congr rfl hrow]
  simp

theorem truncateCentre_split (M : MultiGraph V) (a : V) (μ : ℕ) :
    (M.truncateCentre a μ).addCopies
      (starCopies a (fun v => M.mult s(a,v)-μ) (by rw [M.loopless _ (by simp)];simp)) = M := by
  apply ext_mult
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    change (if a ∈ s(u,v) then min (M.mult s(u,v)) μ else M.mult s(u,v))+
      (if u=a then M.mult s(a,v)-μ else if v=a then M.mult s(a,u)-μ else 0) = M.mult s(u,v)
    by_cases hu : u = a
    · subst u;simp only [Sym2.mem_iff,true_or,if_true]
      omega
    by_cases hv : v = a
    · subst v
      have hswap : M.mult s(u,a) = M.mult s(a,u) := congrArg M.mult Sym2.eq_swap
      simp only [Sym2.mem_iff,or_true,if_true,if_neg hu,hswap]
      omega
    have hmem : a ∉ s(u,v) := by simpa only [Sym2.mem_iff,eq_comm,not_or] using And.intro hu hv
    rw [if_neg hmem,if_neg hu,if_neg hv,add_zero]

theorem star_colourable (a : V) (f : V → ℕ) (hf : f a = 0) :
    Nonempty ((starCopies a f hf).EdgeColoring (∑ v, f v)) := by
  apply exists_edgeColoring_of_bipartite _ {a}
  · intro u v huv
    rw [starCopies_mult]
    by_cases hu : u=a
    · subst u
      have hv : v=a := by simpa using huv.mp (mem_singleton_self a)
      subst v;simp [hf]
    · have hu' : u ∉ ({a} : Finset V) := by simpa only [mem_singleton] using hu
      have hv : v ≠ a := by simpa only [mem_singleton] using (not_iff_not.mpr huv).mp hu'
      rw [if_neg hu,if_neg hv]
  · intro v
    by_cases hv : v=a
    · subst v;rw [degree_starCopies_center]
    · rw [degree_starCopies_other _ _ _ _ hv]
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)

theorem colourable_of_saturated_centre (M : MultiGraph V) (a : V) (μ : ℕ)
    (hoff : ∀ u v, u ≠ a → v ≠ a → M.mult s(u,v) ≤ μ)
    (hsat : ∀ v, v ≠ a → μ ≤ M.mult s(a,v)) :
    Nonempty (M.EdgeColoring (M.degree a+μ)) := by
  let f := fun v => M.mult s(a,v)-μ
  have hf : f a = 0 := by dsimp only [f];rw [M.loopless _ (by simp)];simp
  obtain ⟨C⟩ := colourable_by_order_times_multiplicity (M.truncateCentre a μ) μ
    (Fintype.card_pos_iff.mpr ⟨a⟩) (M.truncateCentre_cap a μ hoff)
  obtain ⟨S⟩ := star_colourable a f hf
  have hsplit := M.truncateCentre_split a μ
  have hdegree := congrArg (fun L : MultiGraph V => L.degree a) hsplit
  rw [degree_addCopies,M.truncateCentre_degree a μ hsat,degree_starCopies_center] at hdegree
  have hn : Fintype.card V-1+1 = Fintype.card V := Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨a⟩)
  have hk : μ*Fintype.card V+(∑ v, f v) = M.degree a+μ := by
    have hm := congrArg (fun n => n*μ) hn
    dsimp only [f] at *
    nlinarith only [hdegree,hm]
  have hc := C.addCopies S
  change Nonempty (M.EdgeColoring (M.degree a+μ))
  rw [hk,hsplit] at hc
  exact ⟨hc⟩

theorem exists_small_centre_bundle_of_not_colourable (M : MultiGraph V) (a : V) (d μ : ℕ)
    (hoff : ∀ u v, u ≠ a → v ≠ a → M.mult s(u,v) ≤ μ) (ha : M.degree a ≤ d)
    (hNo : ¬Nonempty (M.EdgeColoring (d+μ))) :
    ∃ v, v ≠ a ∧ M.mult s(a,v) < μ := by
  by_contra! h
  obtain ⟨C⟩ := M.colourable_of_saturated_centre a μ hoff h
  exact hNo (C.enlarge (by omega))

end SimpleGraph.MultiGraph
