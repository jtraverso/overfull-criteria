module

public import OverfullWork.PriorityCopyAllocation
public import OverfullWork.HeavyPairBoundary

@[expose] public section


/-! # Construct CMS Case 2's first middle copies M0

No-overfullness of the actual triangle pays for q-a copies avoiding
both protected vertices. A prescribed heavy class has strict priority.
The count function represents selected copies, not just a size bound.
-/
namespace OverfullWork.InitialMiddleCopies
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

def allowed (A : Finset V) (b w : V) : Finset V := Aᶜ\{b,w}

structure Selection (M : MultiGraph V) (A H : Finset V) (a b w : V) where
  count : V → ℕ
  capacity : ∀ v, count v ≤ M.mult s(a,v)
  supported : ∀ v, v ∉ allowed A b w → count v = 0
  total : (∑ v, count v) = M.mult s(b,w)-M.degreeInto A a
  priority : (∑ v ∈ H, count v) = min (M.mult s(b,w)-M.degreeInto A a) (M.degreeInto H a)

theorem available_size (M : MultiGraph V) (A : Finset V) (a b w : V) (d : ℕ)
    (hreg : M.IsRegularOfDegree d) (hNo : ¬ M.HasOverfullSubset d)
    (ha : a ∈ A) (hb : b ∉ A) (hw : w ∉ A) (hbw : b ≠ w) :
    M.mult s(b,w)-M.degreeInto A a ≤ M.degreeInto (allowed A b w) a := by
  have hab : a ≠ b := fun he => hb (he ▸ ha)
  have haw : a ≠ w := fun he => hw (he ▸ ha)
  have hPair : ({b,w} : Finset V) ⊆ Aᶜ :=
    insert_subset (mem_compl.mpr hb) (singleton_subset_iff.mpr (mem_compl.mpr hw))
  have hs := sum_sdiff (f := fun v => M.mult s(a,v)) hPair
  rw [sum_pair hbw] at hs
  have hd := M.degreeInto_add_compl A a
  rw [hreg a] at hd
  have ht := HeavyPairBoundary.triple_bundle_le M d hNo a b hab
    ⟨w,(HeavyPairBoundary.mem_outside a b w).mpr ⟨haw.symm,hbw.symm⟩⟩
  change M.mult s(a,b)+M.mult s(a,w)+M.mult s(b,w) ≤ d at ht
  change M.degreeInto (allowed A b w) a+(M.mult s(a,b)+M.mult s(a,w)) =
    M.degreeInto Aᶜ a at hs
  omega

theorem exists_selection (M : MultiGraph V) (A H : Finset V) (a b w : V) (d : ℕ)
    (hreg : M.IsRegularOfDegree d) (hNo : ¬ M.HasOverfullSubset d)
    (ha : a ∈ A) (hb : b ∉ A) (hw : w ∉ A) (hbw : b ≠ w)
    (hH : H ⊆ allowed A b w) : Nonempty (Selection M A H a b w) := by
  let cap : V → ℕ := fun v => if v ∈ allowed A b w then M.mult s(a,v) else 0
  have hCap : (∑ v, cap v) = M.degreeInto (allowed A b w) a := by
    simp [cap,MultiGraph.degreeInto,←sum_filter]
  have hAvailable := available_size M A a b w d hreg hNo ha hb hw hbw
  obtain ⟨f,hf,hTotal,hPriority⟩ := PriorityCopyAllocation.exists_allocation cap H
    (M.mult s(b,w)-M.degreeInto A a) (by rwa [hCap])
  have hPriorityCap : (∑ v ∈ H, cap v) = M.degreeInto H a := by
    exact sum_congr rfl (fun v hv => if_pos (hH hv))
  refine ⟨{ count := f, capacity := ?_, supported := ?_, total := hTotal, priority := ?_ }⟩
  · intro v
    have hh := hf v
    dsimp only [cap] at hh
    split_ifs at hh <;> omega
  · intro v hv
    have hh := hf v
    simp only [cap,if_neg hv] at hh
    omega
  · rwa [hPriorityCap] at hPriority

variable {M : MultiGraph V} {A H : Finset V} {a b w : V}

theorem Selection.centre_zero (s : Selection M A H a b w) (ha : a ∈ A) : s.count a = 0 := by
  apply s.supported
  simp [allowed,ha]

def Selection.graph (s : Selection M A H a b w) (ha : a ∈ A) : MultiGraph V :=
  MultiGraph.starCopies a s.count (s.centre_zero ha)

theorem Selection.graph_le (s : Selection M A H a b w) (ha : a ∈ A) :
    ∀ t, (s.graph ha).mult t ≤ M.mult t := by
  intro t
  induction t using Sym2.inductionOn with
  | hf x y =>
    rw [Selection.graph,MultiGraph.starCopies_mult]
    by_cases hx : x = a
    · subst x; rw [if_pos rfl];exact s.capacity y
    rw [if_neg hx]
    by_cases hy : y = a
    · subst y;rw [if_pos rfl,show s(x,a) = s(a,x) from Sym2.eq_swap];exact s.capacity x
    rw [if_neg hy]
    exact Nat.zero_le _

theorem Selection.graph_centre_degree (s : Selection M A H a b w) (ha : a ∈ A) :
    (s.graph ha).degree a = M.mult s(b,w)-M.degreeInto A a := by
  rw [Selection.graph,MultiGraph.degree_starCopies_center,s.total]

theorem Selection.second_zero (s : Selection M A H a b w) : s.count b = 0 := by
  apply s.supported
  simp [allowed]

theorem Selection.exception_zero (s : Selection M A H a b w) : s.count w = 0 := by
  apply s.supported
  simp [allowed]

theorem Selection.protection_budget (s : Selection M A H a b w) :
    M.mult s(b,w) ≤ M.degreeInto A a + ∑ v, s.count v := by
  rw [s.total]
  omega

end OverfullWork.InitialMiddleCopies
