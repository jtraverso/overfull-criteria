module

public import OverfullWork.KuhnOsthusAssignedPathPartition
public import OverfullWork.KuhnOsthusExceptionalFactorPieces
public import OverfullWork.KuhnOsthusOrdinaryDoubleStyles
public import OverfullWork.KuhnOsthusRoundedStyleBudget
public import Mathlib.Data.Fintype.Option

@[expose] public section


/-! Kühn–Osthus Lemma 8.1, starting from the original complete
exceptional path systems of a uniformly indexed exceptional factor. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

/-- A system indexed by a style and an interval. The fields record the
properties of its original arcs needed in Lemma 8.1. -/
structure OriginalExceptionalFactor (label : V → Fin 50) (Z : Finset V) (l : ℕ) where
  path : Fin 50 × Fin l → Digraph V
  path_system : ∀ i, IsDirectedPathSystem (path i)
  cover : ∀ i, CoversExceptional (path i) Z
  no_internal : ∀ i {x y}, (path i).Adj x y → x ∈ Z → y ∉ Z
  style : ∀ i, SupportedByStyles label Z {i.1} (path i)
  size : ∀ i, (Fintype.card (Arc (path i)) : ℝ) ≤ (Fintype.card V : ℝ) / (50*l) + Z.card
  disjoint : ∀ i j {x y}, (path i).Adj x y → (path j).Adj x y → i = j
  ordinary_out : ∀ i j {x y z}, x ∉ Z →
    (exceptionalPart (path i) Z).Adj x y → (exceptionalPart (path j) Z).Adj x z → y = z
  ordinary_in : ∀ i j {x y z}, x ∉ Z →
    (exceptionalPart (path i) Z).Adj y x → (exceptionalPart (path j) Z).Adj z x → y = z
  ordinary_match : ∀ i j {x y z}, x ∉ Z →
    (exceptionalPart (path i) Z).Adj y x → ¬ (exceptionalPart (path j) Z).Adj x z

/-- The interval positions, together with the residual slot, give
exactly the number of output systems in Lemma 8.1. -/
theorem card_kuhn_osthus_path_slots (l : ℕ) :
    Fintype.card (Option (Fin 50 × Fin l)) = 50*l+1 := by
  rw [Fintype.card_option,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

/-- The original system can use one source per nonfinal ordinary
vertex and one per exceptional vertex. -/
theorem original_exceptional_path_size_from_sources {D : Digraph V} {S Z : Finset V}
    (hD : IsDirectedPathSystem D) (hSource : ∀ x y, D.Adj x y → x ∈ S ∪ Z) :
    Fintype.card (Arc D) ≤ S.card + Z.card := by
  let f (e : Arc D) : ↥(S ∪ Z) := ⟨e.val.1,hSource _ _ e.prop⟩
  have hf : Function.Injective f := by
    intro a b h
    have hx := congrArg (fun v : ↥(S ∪ Z) => (v : V)) h
    change a.val.1 = b.val.1 at hx
    have hb : D.Adj a.val.1 b.val.2 := by rw [hx]; exact b.prop
    exact Subtype.ext (Prod.ext hx (hD.out_unique a.prop hb))
  have hc : Fintype.card (Arc D) ≤ (S ∪ Z).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  exact hc.trans (card_union_le _ _)

private theorem placed_piece_budgets {I K : Type*} (e : K ↪ I) (D : K → Digraph V)
    {label : V → Fin 50} {Z : Finset V} (S : K → Finset (Fin 50)) {p t : ℕ}
    (hSize : ∀ k, Fintype.card (Arc (D k)) ≤ t)
    (hStyles : ∀ k, (S k).card ≤ p ∧ SupportedByStyles label Z (S k) (D k)) :
    ∀ i, Fintype.card (Arc (placePathPieces e D i)) ≤ t ∧
      ∃ U : Finset (Fin 50), U.card ≤ p ∧ SupportedByStyles label Z U (placePathPieces e D i) := by
  intro i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨k,rfl⟩ := hi
    rw [place_path_pieces_at]
    exact ⟨hSize k,S k,hStyles k⟩
  · have he : placePathPieces e D i = ⊥ := by
      ext x y
      exact ⟨fun ⟨k,hk,_⟩ => hi ⟨k,hk⟩,False.elim⟩
    rw [he]
    let : IsEmpty (Arc (⊥ : Digraph V)) := ⟨fun e => e.prop⟩
    refine ⟨by simp,∅,by simp,?_⟩
    rintro x _ (⟨_,hx⟩ | ⟨_,hx⟩) <;> exact False.elim hx

/-- Partition the arcs of the 1-factor and of the original exceptional
factor into one covering path system per slot, plus the residual one. -/
theorem kuhn_osthus_lemma_8_1_with_support
    {l : ℕ} {label : V → Fin 50} {Z : Finset V}
    (C : OriginalExceptionalFactor label Z l) (σ : Equiv.Perm V)
    (hFixed : ∀ x, σ x ≠ x) (hInternal : ∀ x ∈ Z, σ x ∉ Z)
    (hDis : ∀ i x y, (C.path i).Adj x y → σ x ≠ y)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1)) :
    ∃ Q : Option (Fin 50 × Fin l) → Digraph V,
      (∀ x y, (σ x = y ∨ ∃ i, (C.path i).Adj x y) ↔ ∃! i, (Q i).Adj x y) ∧
      (∀ i, IsDirectedPathSystem (Q i) ∧ CoversExceptional (Q i) Z ∧
        (Fintype.card (Arc (Q i)) : ℝ) ≤ 1230 * Fintype.card V / (50*l+1) ∧
        ∃ S : Finset (Fin 50), S.card ≤ 5 ∧ SupportedByStyles label Z S (Q i)) ∧
      Fintype.card (Arc (Q none)) = 2 * Z.card ∧
      ∀ i x y, (Q i).Adj x y → σ x = y ∨ ∃ j, (C.path j).Adj x y := by
  classical
  let n := Fintype.card V
  let s := 50*l+1
  let q := (50*l)/1226
  let t := ⌈(n : ℝ) / q⌉₊
  have hQlow : 1226*q ≤ 50*l := Nat.mul_div_le _ _
  have hQhigh : s ≤ 1226*(q+1) := by
    have h := Nat.lt_mul_div_succ (50*l) (show 0 < 1226 by decide)
    omega
  have hQpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hCapacity : n ≤ q*t := by
    have ht : (n : ℝ) ≤ (q : ℝ) * t := by
      rw [mul_comm]
      exact (div_le_iff₀ hQpos).mp (Nat.le_ceil _)
    exact_mod_cast ht
  obtain ⟨e,a,he,ha,hSlots⟩ := exists_kuhn_osthus_style_schedule
    (show 20 ≤ l by omega) (show 100 ≤ q by omega) hQlow
  obtain ⟨A,hA,hAowner⟩ := exists_ordinary_double_style_pieces σ Z label hFixed
    (show 2 ≤ q by omega) hCapacity
  let H := exceptionalFactorPiece σ label Z
  have hHcover := exceptional_factor_incidences_owners σ label Z hInternal
  have hHside := exceptional_factor_piece_sides σ label Z
  have hHstyle := exceptional_factor_piece_style σ label Z
  have hFreshH (k : Bool × Fin 50) (v : V) (hv : v ∉ Z) (h : IncidentTo (H k) v) :
      ¬ IncidentTo (C.path (e k)) v := by
    apply disjoint_ordinary_vertices_of_styles (hHstyle k) (C.style (e k)) _ v hv h
    exact disjoint_singleton.mpr ((he k).2.symm)
  have hFreshA (k : DoubleStyle × Fin q) (v : V) (h : IncidentTo (A k) v) :
      ¬ IncidentTo (C.path (a k)) v := by
    have hv : v ∉ Z := by
      rcases h with ⟨w,hw⟩ | ⟨w,hw⟩
      · exact ((hA k).2.2.2 _ _ hw).2.1
      · exact ((hA k).2.2.2 _ _ hw).2.2
    apply disjoint_ordinary_vertices_of_styles (hA k).2.2.1 (C.style (a k)) _ v hv h
    exact disjoint_singleton_right.mpr (ha k).2
  have hHdis (i j : Bool × Fin 50) {x y : V} (hi : (H i).Adj x y) (hj : (H j).Adj x y) :
      i = j := by
    have hc := (hHside i).elim (fun h => Or.inl (h hi)) (fun h => Or.inr (h hi))
    obtain ⟨k,_,hk⟩ := (exceptional_factor_arc_owner σ label Z).mp ⟨hi.1,hc⟩
    exact (hk i hi).trans (hk j hj).symm
  have hAdis (i j : DoubleStyle × Fin q) {x y : V} (hi : (A i).Adj x y) (hj : (A j).Adj x y) :
      i = j := by
    obtain ⟨k,_,hk⟩ := (hAowner x y).mp ((hA i).2.2.2 x y hi)
    exact (hk i hi).trans (hk j hj).symm
  obtain ⟨Q,hQ,hOwner,hSup,hCross,hResidual⟩ := exists_path_partition_of_assigned_pieces H A C.path Z
    e a hSlots (exceptional_factor_piece_path_system σ label Z) (fun k => (hA k).1)
    C.path_system C.cover hHside C.no_internal hFreshH hFreshA C.ordinary_out C.ordinary_in
    C.ordinary_match hHcover.1 hHcover.2 hHdis hAdis C.disjoint
    (fun k j x y h g => by
      have hO := (hA j).2.2.2 x y g
      rcases hHside k with hs | hs
      · exact hO.2.1 (hs h).1
      · exact hO.2.2 (hs h).2)
    (fun _ i x y h g => hDis i x y g h.1)
    (fun k i x y h g => hDis i x y g ((hA k).2.2.2 x y h).1)
  have hResidualCard := card_arcs_of_exceptional_cover (hQ none).1 (hQ none).2
    (fun h => hCross _ _ h)
  refine ⟨Q,?_,?_,hResidualCard,?_⟩
  · intro x y
    rw [←hOwner]
    constructor
    · rintro (h | h)
      · by_cases hx : x ∈ Z
        · have hy : y ∉ Z := h ▸ hInternal x hx
          obtain ⟨k,hk,_⟩ := (exceptional_factor_arc_owner σ label Z).mp ⟨h,Or.inl ⟨hx,hy⟩⟩
          exact Or.inl ⟨k,hk⟩
        · by_cases hy : y ∈ Z
          · obtain ⟨k,hk,_⟩ := (exceptional_factor_arc_owner σ label Z).mp ⟨h,Or.inr ⟨hx,hy⟩⟩
            exact Or.inl ⟨k,hk⟩
          · obtain ⟨k,hk,_⟩ := (hAowner x y).mp ⟨h,hx,hy⟩
            exact Or.inr (Or.inl ⟨k,hk⟩)
      · exact Or.inr (Or.inr h)
    · rintro (⟨k,hk⟩ | ⟨k,hk⟩ | h)
      · exact Or.inl hk.1
      · exact Or.inl ((hA k).2.2.2 x y hk).1
      · exact Or.inr h
  · intro i
    refine ⟨(hQ i).1,(hQ i).2,?_⟩
    cases i with
    | none =>
      have hAll : SupportedByStyles label Z ((univ : Finset (Fin 50)).filter (fun j => j.val < 5))
          (Q none) := by
        apply supported_styles_of_residual_slot hResidual
        intro k _ v hv hInc
        have hv' := Finset.mem_singleton.mp (C.style (e k) v hv hInc)
        rw [hv']
        exact mem_filter.mpr ⟨mem_univ _,(he k).1.1⟩
      refine ⟨?_,_,?_,hAll⟩
      · have hcast : (Fintype.card (Arc (Q none)) : ℝ) = 2 * Z.card := by exact_mod_cast hResidualCard
        rw [hcast]
        refine hZ.trans ?_
        have hs : 0 < (50 : ℝ)*l+1 := by positivity
        apply (div_le_div_iff₀ hs hs).mpr
        have hh : (0 : ℝ) ≤ n * (50*l+1) := by positivity
        nlinarith
      · decide
    | some i =>
      obtain ⟨haSize,stylesA,hStylesA,hSupportsA⟩ := placed_piece_budgets a A (fun k => k.1.val)
        (fun k => (hA k).2.1) (fun k => ⟨(mem_powersetCard.mp k.1.prop).2.le,(hA k).2.2.1⟩) i
      obtain ⟨hhSize,hs,hhsSize,hhs⟩ := placed_piece_budgets e H (fun k => {k.2}) (p := 1)
        (card_exceptional_factor_piece σ label Z) (fun k => ⟨by simp,hHstyle k⟩) i
      have hCard : (Fintype.card (Arc (Q (some i))) : ℝ) ≤
          (Fintype.card (Arc (placePathPieces a A i)) : ℝ) +
          Fintype.card (Arc (placePathPieces e H i)) + Fintype.card (Arc (C.path i)) := by
        exact_mod_cast card_arcs_le_of_path_piece_support (hSup i)
      have ha' : (Fintype.card (Arc (placePathPieces a A i)) : ℝ) ≤ t := by exact_mod_cast haSize
      have hh' : (Fintype.card (Arc (placePathPieces e H i)) : ℝ) ≤ Z.card := by exact_mod_cast hhSize
      have hEst := rounded_style_budget (s := s) (n := n) (q := q)
        hL hQhigh (show 3 ≤ s by omega) hN
      have hEst' : (t : ℝ) + n / (50*l) + n / (50*l+1) ≤ 1230 * n / (50*l+1) := by
        simpa only [s,t,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,
          add_sub_cancel_right] using hEst
      have hNum : (Fintype.card (Arc (Q (some i))) : ℝ) ≤ 1230 * n / (50*l+1) := by
        have hc := C.size i
        change (Fintype.card (Arc (C.path i)) : ℝ) ≤ n / (50*l) + Z.card at hc
        change 2 * (Z.card : ℝ) ≤ n / (50*l+1) at hZ
        linarith only [hCard,ha',hh',hc,hZ,hEst']
      refine ⟨?_,stylesA ∪ hs ∪ {i.1},?_,styles_of_path_piece_support (hSup i) hSupportsA hhs (C.style i)⟩
      · exact hNum
      · have hle := (card_union_le (stylesA ∪ hs) {i.1}).trans
          (Nat.add_le_add_right (card_union_le stylesA hs) _)
        rw [card_singleton] at hle
        omega

  · intro i x y h
    cases i with
    | none =>
      obtain ⟨k,hk,_⟩ := hResidual x y h
      exact Or.inr ⟨e k,hk⟩
    | some i =>
      rcases (Digraph.sup_adj _ _ _ _).mp (hSup i h) with hPlaced | hC
      · rcases (Digraph.sup_adj _ _ _ _).mp hPlaced with ⟨k,_,hk⟩ | ⟨k,_,hk⟩
        · exact Or.inl ((hA k).2.2.2 x y hk).1
        · exact Or.inl hk.1
      · exact Or.inr ⟨i,hC⟩

/-- Partition the arcs of the 1-factor and of the original exceptional
factor into one covering path system per slot, plus the residual one. -/
theorem kuhn_osthus_lemma_8_1_of_original_exceptional_factor
    {l : ℕ} {label : V → Fin 50} {Z : Finset V}
    (C : OriginalExceptionalFactor label Z l) (σ : Equiv.Perm V)
    (hFixed : ∀ x, σ x ≠ x) (hInternal : ∀ x ∈ Z, σ x ∉ Z)
    (hDis : ∀ i x y, (C.path i).Adj x y → σ x ≠ y)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1)) :
    ∃ Q : Option (Fin 50 × Fin l) → Digraph V,
      (∀ x y, (σ x = y ∨ ∃ i, (C.path i).Adj x y) ↔ ∃! i, (Q i).Adj x y) ∧
      (∀ i, IsDirectedPathSystem (Q i) ∧ CoversExceptional (Q i) Z ∧
        (Fintype.card (Arc (Q i)) : ℝ) ≤ 1230 * Fintype.card V / (50*l+1) ∧
        ∃ S : Finset (Fin 50), S.card ≤ 5 ∧ SupportedByStyles label Z S (Q i)) ∧
      Fintype.card (Arc (Q none)) = 2 * Z.card := by
  obtain ⟨Q,hQ,hProperties,hSize,_⟩ :=
    kuhn_osthus_lemma_8_1_with_support C σ hFixed hInternal hDis hL hN hZ
  exact ⟨Q,hQ,hProperties,hSize⟩

end OverfullWork.DirectedRobustExpansion
