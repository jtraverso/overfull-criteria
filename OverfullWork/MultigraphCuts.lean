module

public import OverfullWork.MultigraphExtension

@[expose] public section


/-!
# Weighted internal edge counts and cuts

All counts include multiplicities. In a D-regular loopless multigraph,
2 e(S) + cut(S) = D |S|. On an odd set, overfullness is exactly a cut
smaller than D, so complementary odd sets have the same obstruction.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def restrict (M : MultiGraph V) (S : Finset V) : MultiGraph V where
  mult e := if e.toFinset ⊆ S then M.mult e else 0
  loopless e he := by
    split_ifs
    · exact M.loopless e he
    · rfl

def edgesWithin (M : MultiGraph V) (S : Finset V) : ℕ := (M.restrict S).edgeCount

def twiceInternal (M : MultiGraph V) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ S, M.mult s(u,v)

def cutSize (M : MultiGraph V) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, M.mult s(u,v)

def HasOverfullSubset (M : MultiGraph V) (D : ℕ) : Prop :=
  ∃ S : Finset V, D * (S.card / 2) < M.edgesWithin S

def NoOddOverfull (M : MultiGraph V) (D : ℕ) : Prop :=
  ∀ S : Finset V, Odd S.card → M.twiceInternal S ≤ D * (S.card - 1)

theorem degree_restrict (M : MultiGraph V) (S : Finset V) (u : V) :
    (M.restrict S).degree u = if u ∈ S then ∑ v ∈ S, M.mult s(u,v) else 0 := by
  rw [degree_eq_sum_mult]
  simp only [restrict, Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff]
  by_cases hu : u ∈ S
  · simp [hu]
  · simp [hu]

theorem twiceInternal_eq (M : MultiGraph V) (S : Finset V) :
    M.twiceInternal S = 2 * M.edgesWithin S := by
  have h := (M.restrict S).sum_degrees_eq_twice_edgeCount
  simp_rw [degree_restrict] at h
  simpa [twiceInternal, edgesWithin, ← sum_filter] using h

theorem cutSize_compl (M : MultiGraph V) (S : Finset V) : M.cutSize Sᶜ = M.cutSize S := by
  simp only [cutSize, compl_compl]
  rw [sum_comm]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  rw [Sym2.eq_swap]

theorem sum_degree_eq_internal_add_cut (M : MultiGraph V) (S : Finset V) :
    (∑ u ∈ S, M.degree u) = M.twiceInternal S + M.cutSize S := by
  rw [twiceInternal, cutSize, ← sum_add_distrib]
  apply sum_congr rfl
  intro u hu
  rw [degree_eq_sum_mult]
  exact (sum_add_sum_compl S (fun v => M.mult s(u,v))).symm

theorem regular_cut_identity (M : MultiGraph V) {D : ℕ}
    (hreg : M.IsRegularOfDegree D) (S : Finset V) :
    M.twiceInternal S + M.cutSize S = D * S.card := by
  rw [← sum_degree_eq_internal_add_cut]
  calc
    _ = ∑ _u ∈ S, D := sum_congr rfl (fun u _ => hreg u)
    _ = _ := by simp [Nat.mul_comm]

theorem twiceInternal_le_degree_sum (M : MultiGraph V) (S : Finset V) :
    M.twiceInternal S ≤ ∑ u ∈ S, M.degree u := by
  rw [sum_degree_eq_internal_add_cut]
  omega

theorem odd_overfull_iff_small_cut (M : MultiGraph V) {D : ℕ}
    (hreg : M.IsRegularOfDegree D) (S : Finset V) (hodd : Odd S.card) :
    (D * (S.card - 1) < M.twiceInternal S) ↔ M.cutSize S < D := by
  have hc := M.regular_cut_identity hreg S
  have hs : 1 ≤ S.card := by obtain ⟨m, hm⟩ := hodd; omega
  have hsplit : D * (S.card - 1) + D = D * S.card := by
    calc
      _ = D * (S.card - 1 + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hs]
  omega

theorem odd_card_compl {S : Finset V} (heven : Even (Fintype.card V))
    (hodd : Odd S.card) : Odd Sᶜ.card := by
  obtain ⟨a, ha⟩ := heven
  obtain ⟨b, hb⟩ := hodd
  have hle : S.card ≤ Fintype.card V := card_le_univ S
  have hc : S.card + Sᶜ.card = Fintype.card V := by simp only [card_compl]; omega
  refine ⟨a - b - 1, ?_⟩
  omega

theorem complementary_odd_overfull_iff (M : MultiGraph V) {D : ℕ}
    (hreg : M.IsRegularOfDegree D) (heven : Even (Fintype.card V))
    (S : Finset V) (hodd : Odd S.card) :
    (D * (S.card - 1) < M.twiceInternal S) ↔
      D * (Sᶜ.card - 1) < M.twiceInternal Sᶜ := by
  rw [M.odd_overfull_iff_small_cut hreg S hodd,
    M.odd_overfull_iff_small_cut hreg Sᶜ (odd_card_compl heven hodd), M.cutSize_compl]

theorem noOverfull_iff_odd_bounds (M : MultiGraph V) (D : ℕ)
    (hdeg : ∀ v, M.degree v ≤ D) :
    (¬ M.HasOverfullSubset D) ↔ M.NoOddOverfull D := by
  constructor
  · intro h S hodd
    have hs : M.edgesWithin S ≤ D * (S.card / 2) := by
      by_contra hlt
      exact h ⟨S, Nat.lt_of_not_ge hlt⟩
    obtain ⟨m, hm⟩ := hodd
    rw [twiceInternal_eq]
    have hh : S.card / 2 = m := by omega
    have hp : D * (S.card - 1) = 2 * (D * m) := by
      rw [hm]
      have hsub : 2 * m + 1 - 1 = 2 * m := by omega
      rw [hsub]
      ring
    rw [hh] at hs
    rw [hp]
    omega
  · intro h
    rintro ⟨S, hS⟩
    by_cases ho : Odd S.card
    · have hb := h S ho
      rw [twiceInternal_eq] at hb
      obtain ⟨m, hm⟩ := ho
      have hh : S.card / 2 = m := by omega
      have hp : D * (S.card - 1) = 2 * (D * m) := by
        rw [hm]
        have hsub : 2 * m + 1 - 1 = 2 * m := by omega
        rw [hsub]
        ring
      rw [hh] at hS
      rw [hp] at hb
      omega
    · have he : Even S.card := Nat.not_odd_iff_even.mp ho
      obtain ⟨m, hm⟩ := he
      have hb : M.twiceInternal S ≤ D * S.card := by
        calc
          _ ≤ ∑ v ∈ S, M.degree v := M.twiceInternal_le_degree_sum S
          _ ≤ ∑ _v ∈ S, D := sum_le_sum (fun v _ => hdeg v)
          _ = _ := by simp [Nat.mul_comm]
      rw [twiceInternal_eq, hm] at hb
      have hh : S.card / 2 = m := by omega
      rw [hh] at hS
      nlinarith

theorem noOverfull_iff_odd_cut_bound (M : MultiGraph V) {D : ℕ}
    (hreg : M.IsRegularOfDegree D) :
    (¬ M.HasOverfullSubset D) ↔ ∀ S : Finset V, Odd S.card → D ≤ M.cutSize S := by
  rw [M.noOverfull_iff_odd_bounds D (fun v => (hreg v).le)]
  constructor
  · intro h S hodd
    have hb := h S hodd
    by_contra hc
    have hi := (M.odd_overfull_iff_small_cut hreg S hodd).mpr (Nat.lt_of_not_ge hc)
    omega
  · intro h S hodd
    have hb := h S hodd
    by_contra hi
    have hc := (M.odd_overfull_iff_small_cut hreg S hodd).mp (Nat.lt_of_not_ge hi)
    omega

#print axioms regular_cut_identity
#print axioms complementary_odd_overfull_iff
#print axioms noOverfull_iff_odd_bounds

end SimpleGraph.MultiGraph
