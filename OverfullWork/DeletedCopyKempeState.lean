module

public import OverfullWork.MultigraphCopyCritical
public import OverfullWork.CopyColouringExtraction
public import ShannonColouring.Shannon

@[expose] public section


/-! # An actual edge-family Kempe state after deleting one copy

None labels the one uncolored copy; some labels all remaining copies.
The bundle fibres and degrees are exactly the original multigraph's.
Criticality forbids a full coloring of this family. Missing colors at
the bounded-row root number at least mu+1; elsewhere at least mu.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

abbrev FreshCopies (M : MultiGraph V) (u v : V) := Option (GeneralCopies.Copies (M.eraseOne s(u,v)))

noncomputable def freshEnds (M : MultiGraph V) (u v : V) : M.FreshCopies u v → V × V :=
  fun i => match i with
  | none => (u,v)
  | some j => GeneralCopies.ends (M.eraseOne s(u,v)) j

theorem freshEnds_loopless (M : MultiGraph V) (u v : V) (huv : u ≠ v) :
    ∀ i, (M.freshEnds u v i).1 ≠ (M.freshEnds u v i).2 := by
  intro i
  cases i with
  | none => exact huv
  | some i => exact GeneralCopies.loopless _ i

theorem freshEnds_fibre (M : MultiGraph V) (u v : V) (hpos : 0 < M.mult s(u,v)) (e : Sym2 V) :
    (univ.filter (fun i : M.FreshCopies u v =>
      s((M.freshEnds u v i).1,(M.freshEnds u v i).2)=e)).card = M.mult e := by
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_option]
  have hends : ∀ i : GeneralCopies.Copies (M.eraseOne s(u,v)),
      s((M.freshEnds u v (some i)).1,(M.freshEnds u v (some i)).2)=i.1 := by
    intro i
    exact GeneralCopies.endpoints_eq i.1
  simp_rw [hends]
  have hf := GeneralCopies.edge_fibre_card (M.eraseOne s(u,v)) e
  rw [card_eq_sum_ones,sum_filter] at hf
  rw [hf]
  change (if s(u,v)=e then 1 else 0)+(if e=s(u,v) then M.mult e-1 else M.mult e)=M.mult e
  by_cases he : e=s(u,v)
  · subst e;simp only [ite_true];omega
  · rw [if_neg he,if_neg (Ne.symm he),zero_add]

theorem freshEnds_degree (M : MultiGraph V) (u v : V) (hpos : 0 < M.mult s(u,v)) (w : V) :
    ShannonColouring.degree (M.freshEnds u v) w = M.degree w := by
  let E := M.freshEnds u v
  have hsum : (∑ e ∈ univ.filter (fun e : Sym2 V => w ∈ e),
      (univ.filter (fun i : M.FreshCopies u v => s((E i).1,(E i).2)=e)).card) =
      (univ.filter (fun i : M.FreshCopies u v => w ∈ s((E i).1,(E i).2))).card := by
    rw [sum_card_fiberwise_eq_card_filter]
    simp only [mem_filter,mem_univ,true_and]
  have hcard : ShannonColouring.degree E w =
      (univ.filter (fun i : M.FreshCopies u v => w ∈ s((E i).1,(E i).2))).card := by
    dsimp only [ShannonColouring.degree]
    congr 1
    ext i
    simp [ShannonColouring.degree,Sym2.mem_iff,eq_comm]
  rw [hcard,←hsum]
  change _ = ∑ e ∈ univ.filter (fun e : Sym2 V => w ∈ e), M.mult e
  exact sum_congr rfl (fun e _ => M.freshEnds_fibre u v hpos e)

theorem IsCopyCritical.not_fresh_colourable {M : MultiGraph V} {k : ℕ}
    (hc : M.IsCopyCritical k) (u v : V) (hpos : 0 < M.mult s(u,v)) :
    ¬∃ c : M.FreshCopies u v → Fin k,
      ShannonColouring.IsProperEdgeColouring (M.freshEnds u v) c := by
  rintro ⟨c,hc'⟩
  exact hc.uncolourable (GeneralCopies.colourable_of_labelled_family M (M.freshEnds u v) k
    (M.freshEnds_fibre u v hpos) c hc')

theorem IsCopyCritical.exists_deleted_kempe_state {M : MultiGraph V} (d μ : ℕ)
    (hcrit : M.IsCopyCritical (d+μ)) (hdeg : ∀ w, M.degree w ≤ d) (hμ : 0 < μ)
    (u v : V) (hpos : 0 < M.mult s(u,v)) :
    ∃ c : M.FreshCopies u v → Fin (d+μ),
      ShannonColouring.ProperOn (M.freshEnds u v) (univ.erase none) c ∧
      μ+1 ≤ (univ.filter (ShannonColouring.Misses (M.freshEnds u v) (univ.erase none) c u)).card ∧
      ∀ w, μ ≤ (univ.filter (ShannonColouring.Misses (M.freshEnds u v) (univ.erase none) c w)).card := by
  obtain ⟨C⟩ := hcrit.deletion_colourable s(u,v) hpos
  obtain ⟨c₀,hc₀,_⟩ := C.exists_labelled_copy_colouring
  let c : M.FreshCopies u v → Fin (d+μ) := fun i => match i with
    | none => ⟨0,by omega⟩
    | some j => c₀ j
  have hc : ShannonColouring.ProperOn (M.freshEnds u v) (univ.erase none) c := by
    intro i hi j hj hij hInc
    cases i with
    | none => exact False.elim ((mem_erase.mp hi).1 rfl)
    | some i =>
      cases j with
      | none => exact False.elim ((mem_erase.mp hj).1 rfl)
      | some j => exact hc₀ i j (fun he => hij (congrArg some he)) hInc
  have hd : ∀ w, ShannonColouring.degree (M.freshEnds u v) w ≤ d := by
    intro w
    rw [M.freshEnds_degree u v hpos w]
    exact hdeg w
  refine ⟨c,hc,?_,?_⟩
  · have hh := ShannonColouring.card_misses_ge_of_incident hd (notMem_erase none univ) c
      (x := u) (by exact Or.inl rfl : ShannonColouring.Incident (M.freshEnds u v) none u)
    omega
  · intro w
    have hh := ShannonColouring.card_misses_ge hd (univ.erase none) c w
    omega

end SimpleGraph.MultiGraph
