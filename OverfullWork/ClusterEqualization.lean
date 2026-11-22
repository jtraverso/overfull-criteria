module

public import OverfullWork.ClusterLossRedistribution

@[expose] public section


/-! Construct equal fibres by choosing actual subsets, with the entire
extra exceptional cost paid. No regular partition existence is assumed. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRegularPairs
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

noncomputable def equalize (f : V → Option I) (C : I → Finset V) : V → Option I :=
  fun v => match f v with
    | none => none
    | some i => if v ∈ C i then some i else none

theorem cluster_equalize (f : V → Option I) (C : I → Finset V)
    (hSub : ∀ i,C i ⊆ cluster f i) (i : I) : cluster (equalize f C) i=C i := by
  ext v
  simp only [mem_cluster]
  cases hh : f v with
  | none =>
    have hNot : v ∉ C i := by
      intro hv
      have hn := (mem_cluster f i v).mp (hSub i hv)
      rw [hh] at hn;cases hn
    simp [equalize,hh,hNot]
  | some j =>
    by_cases hji : j=i
    · subst j;simp [equalize,hh]
    · have hNot : v ∉ C i := by
        intro hv
        have hn := (mem_cluster f i v).mp (hSub i hv)
        exact hji (Option.some.inj (hh.symm.trans hn))
      simp [equalize,hh,hji,hNot]

theorem exists_equalization (f : V → Option I) (m M : ℕ)
    (hmM : m ≤ M) (hLower : ∀ i,m ≤ (cluster f i).card)
    (hUpper : ∀ i,(cluster f i).card ≤ M) :
    ∃ g : V → Option I,(∀ i,(cluster g i).card=m) ∧
      (∀ i,cluster g i ⊆ cluster f i) ∧
      (exceptional g).card ≤ (exceptional f).card+(M-m)*Fintype.card I := by
  choose C hSub hCard using fun i => exists_subset_card_eq (hLower i)
  let g := equalize f C
  have hSize : ∀ i,(cluster g i).card=m := by
    intro i;rw [cluster_equalize f C hSub];exact hCard i
  refine ⟨g,hSize,?_,?_⟩
  · intro i;rw [cluster_equalize f C hSub];exact hSub i
  · have hOld := order_le f M hUpper
    have hNew := order_eq g m hSize
    have hSplit : M=m+(M-m) := by omega
    nlinarith only [hOld,hNew,hSplit]

theorem regular_equal_fibres (D : Digraph V) (f g : V → Option I) (m M : ℕ)
    (hUpper : ∀ i,(cluster f i).card ≤ M) (hSize : ∀ i,(cluster g i).card=m)
    (hSub : ∀ i,cluster g i ⊆ cluster f i) (hHalf : M ≤ 2*m)
    (i j : I) (ε d : ℝ) (hε : 0 ≤ ε) (hεHalf : ε ≤ 1/2)
    (hUniform : IsUniform D ε (cluster f i) (cluster f j))
    (hDensity : d ≤ density D (cluster f i) (cluster f j)) :
    IsUniform D (2*ε) (cluster g i) (cluster g j) ∧
      d-ε ≤ density D (cluster g i) (cluster g j) := by
  have hScale : ∀ z : I,((cluster f z).card:ℝ)*ε ≤ ((cluster g z).card:ℝ) ∧
      ((cluster f z).card:ℝ)*ε ≤ ((cluster g z).card:ℝ)*(2*ε) := by
    intro z
    have hBound : (cluster f z).card ≤ 2*(cluster g z).card := by rw [hSize];exact (hUpper z).trans hHalf
    have hBoundR : ((cluster f z).card:ℝ) ≤ 2*((cluster g z).card:ℝ) := by exact_mod_cast hBound
    have hh := mul_le_mul_of_nonneg_right hBoundR hε
    have hCap := mul_le_mul_of_nonneg_left hεHalf (Nat.cast_nonneg (cluster f z).card : (0:ℝ) ≤ _)
    constructor <;> nlinarith only [hh,hCap,hBoundR]
  exact ⟨uniform_on_subcells D hUniform (hSub i) (hSub j)
    (hScale i).1 (hScale j).1 (hScale i).2 (hScale j).2 le_rfl,
    (density_on_subcells D hUniform hDensity (hSub i) (hSub j) (hScale i).1 (hScale j).1).le⟩

theorem exists_redistributed_equalization (f : V → Option I) (X : Finset V) (q m M : ℕ)
    (hmM : m ≤ M) (hLower : ∀ i,m+q ≤ (cluster f i).card)
    (hUpper : ∀ i,(cluster f i).card ≤ M) :
    ∃ g : V → Option (retained f X q),
      (∀ i,(cluster g i).card=m) ∧
      (∀ i,cluster g i ⊆ cluster (redistribute f X q) i) ∧
      (exceptional g).card ≤ (exceptional f).card+X.card+
        M*(overloaded f X q).card+(M-m)*(retained f X q).card := by
  have hLo : ∀ i : retained f X q,m ≤ (cluster (redistribute f X q) i).card := by
    intro i
    have hh := (redistributed_cluster_sizes f X q i).2
    have hOrig := hLower i.val
    omega
  have hHi : ∀ i : retained f X q,(cluster (redistribute f X q) i).card ≤ M :=
    fun i => (redistributed_cluster_sizes f X q i).1.trans (hUpper i.val)
  obtain ⟨g,hSize,hSub,hCost⟩ := exists_equalization (redistribute f X q) m M hmM hLo hHi
  have hFirst := redistributed_exceptional_budget f X q M hUpper
  have hIndex : Fintype.card (retained f X q)=(retained f X q).card := Fintype.card_coe _
  rw [hIndex] at hCost
  exact ⟨g,hSize,hSub,by omega⟩

theorem exists_regular_equalization (D : Digraph V) (f : V → Option I) (m M : ℕ)
    (hmM : m ≤ M) (hLower : ∀ i,m ≤ (cluster f i).card)
    (hUpper : ∀ i,(cluster f i).card ≤ M) (hHalf : M ≤ 2*m)
    (ε d : ℝ) (hε : 0 ≤ ε) (hεHalf : ε ≤ 1/2) :
    ∃ g : V → Option I,(∀ i,(cluster g i).card=m) ∧
      (∀ i,cluster g i ⊆ cluster f i) ∧
      (exceptional g).card ≤ (exceptional f).card+(M-m)*Fintype.card I ∧
      (∀ i j,IsUniform D ε (cluster f i) (cluster f j) →
        d ≤ density D (cluster f i) (cluster f j) →
        IsUniform D (2*ε) (cluster g i) (cluster g j) ∧
          d-ε ≤ density D (cluster g i) (cluster g j)) := by
  obtain ⟨g,hSize,hSub,hCost⟩ := exists_equalization f m M hmM hLower hUpper
  exact ⟨g,hSize,hSub,hCost,fun i j hu hd =>
    regular_equal_fibres D f g m M hUpper hSize hSub hHalf i j ε d hε hεHalf hu hd⟩

theorem nonexceptional_property_of_fibre_subsets (f g : V → Option I)
    (hSub : ∀ i,cluster g i ⊆ cluster f i) (P : V → Prop)
    (hP : ∀ v,f v ≠ none → P v) : ∀ v,g v ≠ none → P v := by
  intro v hv
  cases hh : g v with
  | none => exact False.elim (hv hh)
  | some i =>
    have hf := (mem_cluster f i v).mp (hSub i ((mem_cluster g i v).mpr hh))
    exact hP v (by rw [hf];exact Option.some_ne_none i)

end OverfullWork.DirectedClusterQuotient
