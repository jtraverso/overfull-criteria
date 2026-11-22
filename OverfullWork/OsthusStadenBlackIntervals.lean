module

public import OverfullWork.OsthusStadenBlackCuts
public import Mathlib.GroupTheory.Perm.Cycle.Basic

@[expose] public section


/-! The interval following each consecutive red pair. Every black
cluster belongs to one of these intervals if its orbit meets a red pair. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical
variable {U R : Type*}

def IsBlackBetweenPairs (σ : Equiv.Perm U) (start : R → U) (x : U) : Prop :=
  x ∉ Set.range start ∧ x ∉ Set.range (σ ∘ start)

variable [Fintype U]

theorem exists_next_pair (σ : Equiv.Perm U) (start : R → U) (a : R) :
    ∃ k : ℕ, 0 < k ∧ (σ^k) (start a) ∈ Set.range start := by
  refine ⟨orderOf σ,orderOf_pos _,a,?_⟩
  rw [pow_orderOf_eq_one]
  rfl

noncomputable def nextPairDistance (σ : Equiv.Perm U) (start : R → U) (a : R) : ℕ :=
  Nat.find (exists_next_pair σ start a)

theorem nextPairDistance_spec (σ : Equiv.Perm U) (start : R → U) (a : R) :
    0 < nextPairDistance σ start a ∧ (σ^(nextPairDistance σ start a)) (start a) ∈ Set.range start :=
  Nat.find_spec (exists_next_pair σ start a)

theorem nextPairDistance_min (σ : Equiv.Perm U) (start : R → U) (a : R) (j : ℕ)
    (hj : 0 < j) (h : (σ^j) (start a) ∈ Set.range start) :
    nextPairDistance σ start a ≤ j :=
  Nat.find_min' (exists_next_pair σ start a) ⟨hj,h⟩

/-- A first return to the red-pair sources marks the end of the whole
black interval, including clusters beyond the fixed first `p−3`. -/
theorem black_before_next_pair (σ : Equiv.Perm U) (start : R → U) (a : R) (j : ℕ)
    (hlo : 2 ≤ j) (hhi : j < nextPairDistance σ start a) :
    IsBlackBetweenPairs σ start ((σ^j) (start a)) := by
  constructor
  · intro h
    exact (not_le_of_gt hhi) (nextPairDistance_min σ start a j (by omega) h)
  · rintro ⟨b,hb⟩
    have he : (σ^(j-1)) (start a) = start b := by
      apply σ.injective
      change σ (start b) = (σ^j) (start a) at hb
      simpa only [←Equiv.Perm.mul_apply,←pow_succ',show j-1+1 = j by omega] using hb.symm
    exact (not_le_of_gt (show j-1 < nextPairDistance σ start a by omega))
      (nextPairDistance_min σ start a (j-1) (by omega) ⟨b,he.symm⟩)

/-- The last red pair before a black cluster is obtained by minimizing
the distance from a red-pair source. This supplies the interval
coverage needed when applying the merging lemma. -/
theorem every_black_in_pair_interval (σ : Equiv.Perm U) (start : R → U)
    (x : U) (hx : IsBlackBetweenPairs σ start x)
    (hOrbit : ∃ a, σ.SameCycle (start a) x) :
    ∃ a j, 2 ≤ j ∧ j < nextPairDistance σ start a ∧ (σ^j) (start a) = x := by
  have hEx : ∃ j : ℕ, ∃ a, (σ^j) (start a) = x := by
    obtain ⟨a,ha⟩ := hOrbit
    obtain ⟨j,_,hj⟩ := ha.exists_pow_eq'
    exact ⟨j,a,hj⟩
  let j := Nat.find hEx
  obtain ⟨a,ha⟩ := Nat.find_spec hEx
  change (σ^j) (start a) = x at ha
  have hs : 2 ≤ j := by
    by_contra! hs
    have he : j = 0 ∨ j = 1 := by omega
    rcases he with he | he
    · exact hx.1 ⟨a,by simpa only [he,pow_zero,Equiv.Perm.one_apply] using ha⟩
    · exact hx.2 ⟨a,by simpa only [he,pow_one,Function.comp_apply] using ha⟩
  refine ⟨a,j,hs,?_,ha⟩
  by_contra! hNext
  let k := nextPairDistance σ start a
  obtain ⟨hk,b,hb⟩ := nextPairDistance_spec σ start a
  have hkj : k ≤ j := hNext
  have he : (σ^(j-k)) (start b) = x := by
    rw [hb,←Equiv.Perm.mul_apply,←pow_add,show j-k+k = j by omega]
    exact ha
  have hMin : j ≤ j-k := Nat.find_min' hEx ⟨b,he⟩
  change 0 < k at hk
  omega

/-- The full corridors have distinct cluster positions. Equal
positions in two corridors would exhibit an earlier red-pair source
on one of them. -/
theorem pair_interval_location_injective (σ : Equiv.Perm U) (start : R → U)
    (hStart : Function.Injective start) :
    Function.Injective (fun x : Σ a : R, Fin (nextPairDistance σ start a) =>
      (σ^x.2.val) (start x.1)) := by
  have hDiff (a b : R) (i : Fin (nextPairDistance σ start a))
      (j : Fin (nextPairDistance σ start b)) (hlt : i.val < j.val)
      (he : (σ^i.val) (start a) = (σ^j.val) (start b)) : False := by
    have h : (σ^(j.val-i.val)) (start b) = start a := by
      apply (σ^i.val).injective
      rw [←Equiv.Perm.mul_apply,←pow_add,show i.val+(j.val-i.val)=j.val by omega]
      exact he.symm
    have hb := nextPairDistance_min σ start b (j.val-i.val) (by omega) ⟨a,h.symm⟩
    have := j.isLt
    omega
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  change (σ^i.val) (start a) = (σ^j.val) (start b) at h
  rcases lt_trichotomy i.val j.val with hl | hl | hl
  · exact (hDiff a b i j hl h).elim
  · have hab : a = b := by
      apply hStart
      apply (σ^i.val).injective
      simpa only [←hl] using h
    subst b
    have hij : i = j := Fin.ext hl
    subst j
    rfl
  · exact (hDiff b a j i hl h.symm).elim

end OverfullWork.DirectedRobustExpansion
