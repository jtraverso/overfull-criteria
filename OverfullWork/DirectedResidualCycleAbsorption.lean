module

public import OverfullWork.DirectedAbsorberAssembly
public import OverfullWork.PrefactorOpenOrbit
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.OfFn

@[expose] public section


/-! Turn the cycles of a residual factor into disjoint paths and
absorb them, as in the Hamiltonian case of Lo–Patel Theorem 6.1. -/
namespace OverfullWork.DirectedAbsorbingLadder

open Finset Function DirectedPrefactor DirectedListRoutes
open scoped Classical
variable {V W : Type*} [Fintype W] {D : Digraph V}

private theorem request_of_orbit (e : W ↪ V) (σ : Equiv.Perm W)
    (hEdge : ∀ w, D.Adj (e w) (e (σ w))) (x : W) :
    ∃ P : PathRequest D, ∀ v, v ∈ P.vertices ↔ ∃ w ∈ orbit σ x, e w = v := by
  let n := minimalPeriod (σ : W → W) x
  have hn : 0 < n := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts x)
  let m := n-1
  have hm : m+1 = n := Nat.sub_add_cancel hn
  let f := fun i : Fin (m+1) => e ((σ : W → W)^[i.val] x)
  let T := List.ofFn f
  let z := e ((σ : W → W)^[m] x)
  let tail := List.ofFn (fun i : Fin m => e ((σ : W → W)^[i.val+1] x))
  have hT : T = e x :: tail := by
    simp only [T, List.ofFn_succ, f, Fin.val_zero, iterate_zero_apply, Fin.val_succ, tail]
  have hChain : T.IsChain D.Adj := by
    change (List.ofFn f).IsChain D.Adj
    rw [List.isChain_ofFn]
    intro i hi
    change D.Adj (e ((σ : W → W)^[i] x)) (e ((σ : W → W)^[i+1] x))
    rw [iterate_succ_apply']
    exact hEdge _
  have hSimple : T.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he
    apply Fin.ext
    exact iterate_injOn_Iio_minimalPeriod (i.isLt.trans_le hm.le) (j.isLt.trans_le hm.le) (e.injective he)
  have hLast : T.getLast? = some z := by
    have hNonempty : T ≠ [] := by simp [hT]
    rw [List.getLast?_eq_some_getLast hNonempty]
    change some ((List.ofFn f).getLast hNonempty) = some z
    rw [List.getLast_ofFn_succ]
    rfl
  let P : PathRequest D := ⟨e x, z, tail, ⟨hT ▸ hChain, hT ▸ hLast⟩, hT ▸ hSimple⟩
  refine ⟨P, fun v => ?_⟩
  change v ∈ e x :: tail ↔ _
  rw [← hT]
  simp only [T, List.mem_ofFn, f, orbit_eq_forward_trace, mem_image, mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i.val, i.isLt.trans_le hm.le, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨⟨i, hi.trans_le hm.ge⟩, rfl⟩

private theorem orbit_eq_of_common (σ : Equiv.Perm W) {x y w : W}
    (hx : w ∈ orbit σ x) (hy : w ∈ orbit σ y) : orbit σ x = orbit σ y := by
  have h := ((orbit_mem_iff _ _ _).mp hx).trans ((orbit_mem_iff _ _ _).mp hy).symm
  ext z
  rw [orbit_mem_iff, orbit_mem_iff]
  exact ⟨h.symm.trans, h.trans⟩

/-- Paths obtained by cutting one arc per orbit of a directed factor,
with exact coverage of the vertex type being embedded. -/
theorem requests_of_directed_factor (e : W ↪ V) (σ : Equiv.Perm W)
    (hEdge : ∀ w, D.Adj (e w) (e (σ w))) :
    ∃ requests : List (PathRequest D),
      requests.length = ((univ : Finset W).image (orbit σ)).card ∧
      requests.Pairwise (fun P Q => List.Disjoint P.vertices Q.vertices) ∧
      ∀ v, v ∈ requests.flatMap PathRequest.vertices ↔ v ∈ Set.range e := by
  classical
  let O := (univ : Finset W).image (orbit σ)
  have hRep : ∀ o : O, ∃ x, orbit σ x = o.val := by
    intro o
    obtain ⟨x, _, hx⟩ := mem_image.mp o.prop
    exact ⟨x, hx⟩
  choose x hx using hRep
  choose P hP using fun o : O => request_of_orbit e σ hEdge (x o)
  have hSupport : ∀ o v, v ∈ (P o).vertices ↔ ∃ w ∈ o.val, e w = v := by
    intro o v
    rw [hP, hx]
  let T := O.attach.toList
  have hSize : (T.map P).length = O.card := by simp [T]
  have hDisj : ∀ a b : O, a ≠ b → List.Disjoint (P a).vertices (P b).vertices := by
    intro a b h v ha hb
    obtain ⟨w, hw, rfl⟩ := (hSupport a v).mp ha
    obtain ⟨z, hz, he⟩ := (hSupport b (e w)).mp hb
    have hzEq := e.injective he
    subst z
    have hxw : w ∈ orbit σ (x a) := (hx a).symm ▸ hw
    have hyw : w ∈ orbit σ (x b) := (hx b).symm ▸ hz
    exact h (Subtype.ext ((hx a).symm.trans ((orbit_eq_of_common σ hxw hyw).trans (hx b))))
  refine ⟨T.map P, hSize, List.pairwise_map.mpr (O.attach.nodup_toList.imp (fun h => hDisj _ _ h)), ?_⟩
  intro v
  constructor
  · intro hv
    obtain ⟨R, hR, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp hR
    obtain ⟨w, _, hw⟩ := (hSupport o v).mp hv
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    have hw : w ∈ orbit σ w := (orbit_mem_iff _ _ _).mpr (Equiv.Perm.SameCycle.refl _ _)
    let o : O := ⟨orbit σ w, mem_image_of_mem _ (mem_univ _)⟩
    exact List.mem_flatMap.mpr ⟨P o, List.mem_map.mpr ⟨o, by simp [T], rfl⟩,
      (hSupport o _).mpr ⟨w, hw, rfl⟩⟩

/-- An absorbing cycle and a residual factor with sufficiently few
orbits give a spanning directed cycle of the actual host. -/
theorem AbsorbingCycle.hamilton_of_residual_factor {d : ℕ}
    (C : AbsorbingCycle D d) (e : W ↪ V)
    (hRange : ∀ v, v ∈ Set.range e ↔ v ∉ C.vertices)
    (σ : Equiv.Perm W)
    (hEdge : ∀ v, D.Adj (e v) (e (σ v)))
    (hCount : ((univ : Finset W).image (orbit σ)).card ≤ d) :
    ∃ T : List V, T.Nodup ∧ (∀ v, v ∈ T) ∧ T.head? = some C.root ∧
      (T ++ [C.root]).IsChain D.Adj := by
  obtain ⟨paths, hLen, hDisj, hCover⟩ := requests_of_directed_factor e σ hEdge
  have hOutside : ∀ P ∈ paths, List.Disjoint C.vertices P.vertices := by
    intro P hP w hw hwP
    exact (hRange w).mp ((hCover w).mp (List.mem_flatMap.mpr ⟨P, hP, hwP⟩)) hw
  obtain ⟨T, hT, hSimple, hHead, hClosed⟩ := C.absorbs paths (hLen ▸ hCount) hDisj hOutside
  refine ⟨T, hSimple, fun v => hT.mem_iff.mpr ?_, hHead, hClosed⟩
  apply List.mem_append.mpr
  by_cases hv : v ∈ C.vertices
  · exact Or.inl hv
  · exact Or.inr ((hCover v).mpr ((hRange v).mpr hv))

end OverfullWork.DirectedAbsorbingLadder
